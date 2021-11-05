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
COLOR_HEAD = "darkgreen"
COLOR_TAG = "yellow2"
COLOR_BRANCH = "orange"
COLOR_STASH = "red"

pattern = re.compile(r'^\[(\d+)\|\|(.*)\|\|(.*)\|\|\s?(.*)\]\s([0-9a-f]*)\s?([0-9a-f]*)\s?([0-9a-f]*)$')
revertMessagePattern = re.compile(r'Revert "(.*)"')

parser = argparse.ArgumentParser()

parser.add_argument("-x", "--debug", dest="debug", action="store_true", help="Show debug messages on stderr")
parser.add_argument("-m", "--messages", dest="messages", action="store_true", help="Show commit messages in node" )
parser.add_argument("-r", "--range", help="git commit range" )

args = parser.parse_args()
debug = args.debug

def log(message):
    if debug:
        print(message, file=sys.stderr)


revRange = ""
if args.range:
    revRange = " " + args.range
    log("Range: " + revRange)

gitLogCommand = 'git log --pretty=format:"[%ct||%cn||%s||%d] %h %p" --all ' + revRange
log('Git log command: ' + gitLogCommand)
output = subprocess.Popen(gitLogCommand, shell=True, stdout=subprocess.PIPE, universal_newlines=True)
(out, err) = output.communicate()
lines = out.split("\n")

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
            log("Revert commit")
            match = re.match(revertMessagePattern, message)
            if match:
                originalMessage = match.group(1)
                log("Revert match [" + originalMessage + "]")
                origRevertHash = messages[originalMessage]
                #print('    "' + commitHash + '"->"' + str(origRevertHash) + '"[label="Revert",style=dotted,fontcolor="azure4",color="azure4"]')
                print('    "' + str(origRevertHash) + '"->"' + commitHash + '"[label="Revert",style=dotted,fontcolor="azure4",color="azure4"]')
            nodeColor = COLOR_NODE_REVERT

        nodeInfo = ""
        if ref:
            refEntries = ref.replace("(", "").replace(")", "").split(",")
            for refEntry in refEntries:
                style = "shape=oval,fillcolor=" + COLOR_BRANCH
                if "HEAD" in refEntry:
                    style = "shape=diamond,fillcolor=" + COLOR_HEAD
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
        print("    \"" + commitHash + "\"[label=\"" + commitHash + nodeMessage + labelExt + "\\n(" + user + ")\",shape=box,style=filled,fillcolor=" + nodeColor + "];" + link + link2)
        if nodeInfo:
            print(nodeInfo)
print("}")

