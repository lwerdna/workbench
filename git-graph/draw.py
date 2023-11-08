#!/usr/bin/python3

import os
import re
import sys
import hashlib
import tempfile
import subprocess

# colors
COLOR_NODE = "cornsilk"
COLOR_NODE_MERGE = "cornsilk2"
COLOR_NODE_FIRST = "cornflowerblue"
COLOR_NODE_CHERRY_PICK = "burlywood1"
COLOR_NODE_REVERT = "azure4"
COLOR_HEAD = "green"
COLOR_TAG = "yellow2"
COLOR_BRANCH = "orange"
COLOR_STASH = "red"

pattern = re.compile(r'^\[(\d+)\|\|(.*)\|\|(.*)\|\|\s?(.*)\]\s([0-9a-f]*)\s?([0-9a-f]*)\s?([0-9a-f]*)$')
revertMessagePattern = re.compile(r'Revert "(.*)"')

# configuration
cfg = {
    'commits_back': 12,
    'include_test_branches': 'no',
    'include_remote_tracking_branches': 'no',
    'output_file_path': '/tmp/tmp.dot',
    'commit_msg_width': 12
}
(tmp_handle, tmp_name) = tempfile.mkstemp(suffix='.ini')
print("writing temporary contents to %s" % tmp_name)
tmp_obj = os.fdopen(tmp_handle, 'w')
for key, val in cfg.items():
    tmp_obj.write(f'{key} = {val}\n')
tmp_obj.close()
print("invoking vim and waiting... (gvim %s)" % tmp_name)
subprocess.call(["vim", '-f', tmp_name])
print("reading changes from %s" % tmp_name)
fp = open(tmp_name)
for line in fp.readlines():
    key, val = re.match(r'([^\s]*?)\s*=\s*(.*)', line.strip()).group(1, 2)
    if val in ['no', 'No', 'false', 'False']: val = False
    elif val in ['yes', 'Yes', 'true', 'True']: val = True
    elif re.match(r'^\d+$', val): val = int(val)
    elif re.match(r'^[\d\.]+$', val): val = float(val)
    cfg[key] = val
fp.close()

def log(message):
    print(message, file=sys.stderr)

lines = set()

if cfg['commits_back']:
    log(f'collecting {cfg["commits_back"]} commits back from each branch')
    HEAD = None
    branches = []
    pipe = subprocess.Popen('git branch --all --list --verbose', shell=True, stdout=subprocess.PIPE, universal_newlines=True)
    (out, err) = pipe.communicate()
    for line in out.split('\n'):
        if not line or line.isspace():
            continue

        # HEAD is detached *AT* a particular commit, get that commit
        #
        if m := re.match(r'^\* \(HEAD detached at (.*)\)', line):
            HEAD = m.group(1)
            branches.append(m.group(1))
            continue

        # HEAD is detached *FROM* a particular commit, ignore commit and find where it's at, eg: get 4c1edc0 from:
        # "* (HEAD detached from 115d72f)                       4c1edc0 Lift ENC_LD2_ASISDLSE_R2"
        if m := re.match(r'^\* \(HEAD detached from .*\)\s+([a-fA-F0-9]+)', line):
            HEAD = m.group(1)
            branches.append(m.group(1))
            continue

        # HEAD is at a named branch, eg:
        # "* hehe                                               4c1edc0 Lift ENC_LD2_ASISDLSE_R2"
        if m := re.match(r'^\* ([^ ]+) ', line):
            HEAD = m.group(1)
            branches.append(m.group(1))
            continue

        m = re.match(r'^  ([^ ]+) ', line)
        assert m, breakpoint()
        branches.append(m.group(1))

    assert HEAD
    log('found HEAD: ' + HEAD)
    log('found branches:\n' + '\n'.join(branches))
    #breakpoint()
    #sys.exit(-1)
    for branch in branches:
        if not cfg["include_test_branches"] and (branch.startswith('test_') or branch.startswith('remotes/origin/test_')):
            log(f'skipping branch "{branch}" because it contains "test_"')
            continue
        if not cfg["include_remote_tracking_branches"] and (branch.startswith('remotes/origin/')):
            log(f'skipping branch "{branch}" because it\'s remote tracking')
            continue

        log('collecting commits from %s' % branch)
        # https://git-scm.com/docs/pretty-formats
        # ct = committer date, UNIX timestamp
        # cn = committer name
        # s = subject
        # d = ref names
        # h = abbreviated commit hash
        # p = abbreviated parent hashes
        cmd = 'git log --pretty=format:"[%%ct||%%cn||%%s||%%d] %%h %%p" -n %d %s' % (cfg['commits_back'], branch)
        log(cmd)
        pipe = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, universal_newlines=True)
        (out, err) = pipe.communicate()
        lines.update(out.split("\n"))
else:
    gitLogCommand = 'git log --pretty=format:"[%ct||%cn||%s||%d] %h %p" --all '
    log('Git log command: ' + gitLogCommand)
    pipe = subprocess.Popen(gitLogCommand, shell=True, stdout=subprocess.PIPE, universal_newlines=True)
    (out, err) = pipe.communicate()
    lines = set(out.split("\n"))

lines = list(lines)

dates = {}
messages = {}
predefinedNodeColor = {}

def getCommitDiff(hash):
    # get only the changed lines (starting with + or -), no line numbers, hashes, ...
    command = 'git diff ' + hash + '^ ' + hash + ' | grep "^[-+]"'
    log("Hash Command: " + command)
    diffOutput = subprocess.Popen(command, shell=True, stdout=subprocess.PIPE, universal_newlines=True)
    (diff, err) = diffOutput.communicate()
    return diff

def getCommitDiffHash(hash):
    diff = getCommitDiff(hash)
    sha = hashlib.sha1(diff.encode('utf-8'))
    return sha.hexdigest()

fp = open(cfg['output_file_path'], 'w')
fp.write('digraph G {\n')
fp.write('\trankdir="RL"\n')

# map subjects to abbreviated hashes
# {
#   'more junk': 'c236dd6'
#   'little more assembler work': '14b37bc'
#   'start assembler': '6a5e72a'
#   ... }
#
# map abbreviated hashes to date
# {
#   'a340377': '1440645583'
#   'a512254': '1440645521'
#   '978ed20': '1440644920'
#   ... }
#
for line in lines:
    log('processing line -%s-' % line)
    if not line or line.isspace(): continue
    match = re.match(pattern, line)
    if match:
        date = match.group(1)
        message = match.group(3)
        commitHash = match.group(5)
        if message in messages:
            existing = messages[message]
            #print(dates[existing]+" - "+date)
            if dates[existing] > date:
                #print("setting message ["+message+"] with ["+hash+"]")
                messages[message] = commitHash
        else:
            messages[message] = commitHash
        dates[commitHash] = date
    else:
        #breakpoint()
        raise Exception("malformed line: %s" % line)

for line in lines:
    # line is like:
    # [<date>||<name>||<subject>||] <commit hash> <parent hashes>
    # [1664915022||Glenn Smith||Fix Clang parser decaying array types to pointers in some cases||] 674394d45 c1edaa6a0
    match = re.match(pattern, line)
    if match:
        date, user, message, ref, commitHash, parentHash1, parentHash2 = match.group(1, 2, 3, 4, 5, 6, 7)

        link = ""
        link2 = ""
        labelExt = ""
        nodeMessage = message.replace("\"", "'")[0: cfg['commit_msg_width']];
        if commitHash in predefinedNodeColor:
            labelExt = "\\nSTASH INDEX"
            nodeColor = predefinedNodeColor[commitHash]
        else:
            nodeColor = COLOR_NODE

        if parentHash1:
            link = " \"" + commitHash + "\"->\"" + parentHash1 + "\";"
        else:
            nodeColor = COLOR_NODE_FIRST

        if parentHash2:
            link2 = " \"" + commitHash + "\"->\"" + parentHash2 + "\";"

        if parentHash1 and parentHash2:
            nodeColor = COLOR_NODE_MERGE

        nodeInfo = ""

        # if branches reference this node, add to it
        if ref:
            # '(master)' -> ['master']
            # '(origin/set-default-arch-menu, set-default-arch-menu)' -> ['origin/set-default-arch-menu', 'set-default-arch-menu']
            #
            queue = ref.replace("(", "").replace(")", "").split(", ")
            while queue:
                refEntry = queue.pop(0)
                style = "shape=oval,fillcolor=" + COLOR_BRANCH
                if 'HEAD' in refEntry:
                    if refEntry == 'HEAD':
                        style = "shape=box,fillcolor=" + COLOR_HEAD
                    elif refEntry.startswith("HEAD -> "):
                        refEntry = refEntry[8:]
                        queue.append('HEAD')
                    elif refEntry.endswith('/HEAD'):
                        style = "shape=box,fillcolor=" + COLOR_HEAD
                    else:
                        breakpoint()
                elif "tag" in refEntry:
                    refEntry = refEntry.replace("tag: ", "")
                    style = "shape=oval,fillcolor=" + COLOR_TAG
                elif "stash" in refEntry:
                    style = "shape=box,fillcolor=" + COLOR_STASH
                    nodeColor = COLOR_STASH
                    labelExt = "\\nSTASH"
                    if getCommitDiff(parentHash1) == "":
                        log('>>> "' + parentHash1 + '"[color=red]')
                        predefinedNodeColor[parentHash1] = COLOR_STASH
                    elif getCommitDiff(parentHash2) == "":
                        log('>>> "' + parentHash2 + '"[color=red]')
                        predefinedNodeColor[parentHash2] = COLOR_STASH
                    continue

                nodeInfo += '    "' + refEntry + ' "[style=filled,' + style + ']; "' + refEntry + '" -> "' + commitHash + '"\n'


        fp.write("    \"" + commitHash + "\" [label=\"" + commitHash + nodeMessage + labelExt + "\",shape=box,style=filled,fillcolor=" + nodeColor + "];" + link + link2 + '\n')
        if nodeInfo:
            fp.write(nodeInfo + '\n')
fp.write("}\n")

fp.close()

