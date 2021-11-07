#!/usr/bin/env python

import os, sys, re, pprint, subprocess
import argparse
import subprocess

import networkx as nx

DEBUG=True

def log(msg):
    global DEBUG
    if not DEBUG: return
    print('//', msg)

def get_output_lines(cmd):
    log('running: ' + cmd)
    pipe = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, universal_newlines=True)
    (out, err) = pipe.communicate()
    return [l.strip() for l in out.split('\n')]

def get_branches(remotes_too=False):
    unresolved = {}

    branches = {}
    cmd = 'git branch --list --verbose'
    if remotes_too:
        cmd += ' --all'
    for line in get_output_lines(cmd):
        if not line: continue
        marked_head = False
        if line.startswith('*'):
            marked_head = True
            line = ' ' + line[1:]
        if ' -> ' in line:
            # eg: remotes/origin/HEAD -> origin/dev
            m = re.match('^\s*([^\s]+)\s+-> (.*)$', line)
            (branch_name, link_name) = m.group(1, 2)
            unresolved[branch_name] = link_name
        else:
            m = re.match('^\s*([^\s]+)\s+([^\s]+)\s+(.*)$', line)
            (branch_name, commit, descr) = m.group(1,2,3)
            branches[branch_name] = commit
            if marked_head:
                branches['HEAD'] = commit

    for (branch_name, link_name) in unresolved.items():
        if link_name in branches:
            branches[branch_name] = branches[link_name]
        else:
            branches[branch_name] = branches['remotes/'+link_name]

    return branches

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--disclude-message", action='store_true', dest="disclude_message", help="disclude commit message in nodes")
    parser.add_argument("--disclude-hash", action='store_true', dest="disclude_hash", help="disclude commit hash in nodes")
    parser.add_argument("--include-author", action='store_true', dest="include_author", help="include author in nodes")
    parser.add_argument("--remote-branches", action='store_true', dest="remote_branches", help="include remote branches also")
    parser.add_argument("--message-length", dest="message_length", type=int, default=24, help="how many characters of commit message to include")
    parser.add_argument("--collapse-threshold", dest="collapse_threshold", type=int, default=10, help="length needed for linear run of commits to be collapsed")
    parser.add_argument("-b", "--back", type=int, default=16, help="how many commits back from each ref")
    parser.add_argument("--debug", action='store_true', dest="debug", help="print debugging messages")
    args = parser.parse_args()

    log('settings:')
    log('debug messages? %s' % args.debug)
    log('include remote branches? %s' % args.remote_branches)
    log('disclude message from nodes? %s' % args.disclude_message)
    log('disclude hash from nodes? %s' % args.disclude_hash)
    log('include author in nodes? %s' % args.include_author)
    log('message length in each node: %d' % args.message_length)
    log('commits from each reference: %d' % args.back)

    branches = get_branches(args.remote_branches)
    for (branch_name, commit) in branches.items():
        log('%s @%s' % (branch_name, commit))

    # collect commits
    commits = {}
    pattern = re.compile(r'^\[(\d+)\|\|(.*)\|\|(.*)\|\|\s?(.*)\]\s([0-9a-f]*)\s?(.*)$')
    for start_point in set(branches.values()):
        cmd = 'git log --pretty=format:"[%%ct||%%cn||%%s||%%d] %%h %%p" -n %d %s' % (args.back, start_point)
        for line in get_output_lines(cmd):
            m = re.match(pattern, line)
            if not m:
                breakpoint()
            hash_ = m.group(5)
            if hash_ in commits:
                continue
            parent_hashes = [x for x in m.group(6).split(' ') if x]
            entry = {'hash':hash_, 'date':m.group(1), 'author':m.group(2), 'message':m.group(3),
                        'ref_names':m.group(4), 'hash':hash_, 'parent_hashes':parent_hashes}
            commits[hash_] = entry

    # add placeholder commits for missing parents
    parent_hashes = sum([entry['parent_hashes'] for entry in commits.values()], [])
    absent_parents = set([ph for ph in parent_hashes if not ph in commits])

    # convert to a networkx graph
    DG = nx.DiGraph()
    # nodes
    for c in commits:
        DG.add_node('commit:' + c) # commits identified by hash
    for ap in absent_parents:
        DG.add_node('absent:' + ap) # dummy "absent parent" commit identified by hash of parent it replaces
    for branch_name in branches:
        DG.add_node('branch:' + branch_name)
    # edges
    for (h, cinfo) in commits.items():
        for parent in cinfo['parent_hashes']:
            src = 'commit:'+h
            dst = ('commit:' if parent in commits else 'absent:')+parent
            DG.add_edge(src, dst)
    for branch_name in branches:
        src = 'branch:'+branch_name
        dst = 'commit:'+branches[branch_name]
        DG.add_edge(src, dst)



    # draw graph
    print('digraph DG {')
    print('\trankdir="RL"')
    # nodes
    print('\t// nodes')
    for node in DG.nodes:
        label_lines = []
        attribs = ['style=filled']

        if node.startswith('commit:'):
            attribs.append('shape=box')

            info = commits[node[7:]]

            if not args.disclude_hash:
                label_lines.append(info['hash'])
            if args.include_author:
                label_lines.append('(%s)' % info['author'])
            if not args.disclude_message:
                message_prepared = info['message']
                if len(message_prepared) > args.message_length:
                    message_prepared = message_prepared[0:args.message_length] + '...'
                message_prepared = message_prepared.replace('"', '\\"')
                label_lines.append(message_prepared)

            if info['parent_hashes']:
                attribs.append('fillcolor=cornsilk')
            else:
                attribs.append('fillcolor=cornflowerblue')

        elif node.startswith('absent:'):
            attribs.append('shape=box')
            attribs.append('fillcolor=cornsilk')
            label_lines.append('...')

        elif node.startswith('collapsed:'):
            attribs.append('shape=box')
            attribs.append('fillcolor=cornsilk')
            label_lines.append('...')

        elif node.startswith('branch:'):
            branch_name = node[7:]
            color = 'green' if 'HEAD' in branch_name else 'orange'
            attribs.append('shape=oval')
            attribs.append('fillcolor='+color)
            label_lines.append(branch_name)

        attribs.append('label="' + '\\n'.join(label_lines) + '"')
        print('\t"%s" [%s];' % (node, ','.join(attribs)))
    # edges
    print('\t// edges')
    for edge in DG.edges():
        print('\t"%s" -> "%s";' % (edge[0], edge[1]))
    # done
    print('}')

