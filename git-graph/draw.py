#!/usr/bin/python3

# from https://github.com/daolis/git-graph

__author__ = 'Stephan Bechter <stephan@apogeum.at>'
import subprocess
import re
import hashlib
import sys
import argparse

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

parser = argparse.ArgumentParser()

parser.add_argument("-x", "--debug", dest="debug", action="store_true", help="Show debug messages on stderr")
parser.add_argument("-m", "--messages", dest="messages", action="store_true", help="Show commit messages in node" )
parser.add_argument("-r", "--range", help="git commit range" )
parser.add_argument("-b", "--back", nargs='?', type=int, dest="back", action="store", help="how many commits back from each ref")
args = parser.parse_args()
debug = args.debug
back = args.back

# 'cause it's too fucking hard to make a simple default value in argparse
if not back:
    back = 12

def log(message):
    if debug:
        print(message, file=sys.stderr)

lines = set()

if back:
    log(f'collecting {back} commits back from each branch')
    HEAD = None
    branches = []
    #pipe = subprocess.Popen('git branch --all --list', shell=True, stdout=subprocess.PIPE, universal_newlines=True)
    pipe = subprocess.Popen('git branch --list', shell=True, stdout=subprocess.PIPE, universal_newlines=True)
    (out, err) = pipe.communicate()
    for line in out.split('\n'):
        is_head = False

        line = line.strip()

        # "* master" -> "master"
        # "* (HEAD detached from b2b5b84)" -> "(HEAD detached from b2b5b84)"
        if line.startswith('* '):
            line = line[2:]
            is_head = True

        # "(HEAD detached from b2b5b84)" -> "b2b5b84"
        if line.startswith('(HEAD detached '):
            m = re.match(r'^\(HEAD detached (?:at|from) (.*)\)', line)
            line = m.group(1)

        if not line:
            continue
        if is_head:
            HEAD = line
        branches.append(line)

    #print('found HEAD:', HEAD)
    log('found branches:\n' + '\n'.join(branches))
    #sys.exit(-1)
    for branch in branches:
        log('collecting commits from %s' % branch)
        cmd = 'git log --pretty=format:"[%%ct||%%cn||%%s||%%d] %%h %%p" -n %d %s' % (back, branch)
        log(cmd)
        pipe = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, universal_newlines=True)
        (out, err) = pipe.communicate()
        lines.update(out.split("\n"))
    assert HEAD
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

print("digraph G {")
print('\trankdir="RL"')

# create mapping messages:
# {
#   'more junk': 'c236dd6'
#   'little more assembler work': '14b37bc'
#   'start assembler': '6a5e72a'
#   ... }
#
# create mapping dates
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
    #print(line)
    match = re.match(pattern, line)
    if match:
        date = match.group(1)
        user = match.group(2)
        message = match.group(3)
        ref = match.group(4)
        commitHash = match.group(5)
        parentHash1 = match.group(6)
        parentHash2 = match.group(7)

        if not message in messages:
            breakpoint()

        link = ""
        link2 = ""
        labelExt = ""
        nodeMessage = ""
        if args.messages:
            nodeMessage = "\n" + message.replace("\"", "'");
        if commitHash in predefinedNodeColor:
            labelExt = "\\nSTASH INDEX"
            nodeColor = predefinedNodeColor[commitHash]
        else:
            nodeColor=COLOR_NODE

        if parentHash1:
            #link = " \"" + parentHash1 + "\"->\"" + commitHash + "\";"
            link = " \"" + commitHash + "\"->\"" + parentHash1 + "\";"
        else:
            #initial commit
            nodeColor = COLOR_NODE_FIRST

        if parentHash2:
            #link2 = " \"" + parentHash2 + "\"->\"" + commitHash + "\";"
            link2 = " \"" + commitHash + "\"->\"" + parentHash2 + "\";"

        if parentHash1 and parentHash2:
            nodeColor = COLOR_NODE_MERGE

        # disagree here, message is very often repeated, eg:
        #  "Merge branch 'master' of github.com:user/branch"
        # and does not indicate a cherry pick
        if False and message in messages:
            # message exists in history - possible cherry-pick -> compare diff hashes
            existingHash = messages[message]
            if commitHash is not existingHash and date > dates[existingHash]:
                log('commitHash:%s != existingHash:%s' % (commitHash, existingHash))
                breakpoint()
                diffHashOld = getCommitDiffHash(existingHash)
                diffHashActual = getCommitDiffHash(commitHash)
                log("M [" + message + "]")
                log("1 [" + diffHashOld + "]")
                log("2 [" + diffHashActual + "]")
                if diffHashOld == diffHashActual:
                    log("equal")
                    #print('    "' + str(existingHash) + '"->"' + commitHash + '"[label="Cherry\\nPick",style=dotted,fontcolor="red",color="red"]')
                    print('    "' + commitHash + '"->"' + str(existingHash) + '"[label="Cherry\\nPick",style=dotted,fontcolor="red",color="red"]')
                    nodeColor = COLOR_NODE_CHERRY_PICK
                    #labelExt = "\\nCherry Pick"
                log("")
        log("Message: [" + message + "]")

        if message.startswith("Revert"):
            # check for revert
            log("Revert commit: %s: %s" % (commitHash, message))
            match = re.match(revertMessagePattern, message)
            if match and match.group(1) in messages:
                originalMessage = match.group(1)
                log("Revert match [" + originalMessage + "]")
                origRevertHash = messages[originalMessage]
                #print('    "' + commitHash + '"->"' + str(origRevertHash) + '"[label="Revert",style=dotted,fontcolor="azure4",color="azure4"]')
                print('    "' + str(origRevertHash) + '"->"' + commitHash + '"[label="Revert",style=dotted,fontcolor="azure4",color="azure4"]')
            nodeColor = COLOR_NODE_REVERT

        nodeInfo = ""
        if ref:
            queue = ref.replace("(", "").replace(")", "").split(",")
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
                #else:
                    #if "origin" in refEntry:
                    #    continue
                nodeInfo += '    "' + refEntry + '"[style=filled,' + style + ']; "' + refEntry + '" -> "' + commitHash + '"\n'
        #print("    \"" + commitHash + "\" [label=\"" + commitHash + nodeMessage + labelExt + "\\n(" + user + ")\\n" + message[0:24] + "\",shape=box,style=filled,fillcolor=" + nodeColor + "];" + link + link2)

        message_prepared = message[0:24]
        message_prepared = message_prepared.replace('"', '\\"')
        print("    \"" + commitHash + "\" [label=\"" + commitHash + nodeMessage + labelExt + "\\n" + message_prepared + "\",shape=box,style=filled,fillcolor=" + nodeColor + "];" + link + link2)
        if nodeInfo:
            print(nodeInfo)
print("}")

