#!/usr/bin/env python

import os, sys, re, pprint, subprocess
import argparse
import subprocess

import networkx as nx

DEBUG=False

def log(msg):
    global DEBUG
    if not DEBUG: return
    print(msg)

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
    parser.add_argument("--remote-branches", action='store_true', dest="remote_branches", help="include remote branches also")
    parser.add_argument("--message-length", dest="message_length", type=int, default=24, help="how many characters of commit message to include")
    parser.add_argument("-b", "--back", type=int, default=16, help="how many commits back from each ref")
    args = parser.parse_args() 

    log('settings:')
    log('include remote branches? %s' % args.remote_branches)
    log('disclude message from nodes? %s' % args.disclude_message)
    log('disclude hash from nodes? %s' % args.disclude_hash)
    log('message length in each node: %d' % args.message_length)
    log('commits from each reference: %d' % args.back)

    branches = get_branches(args.remote_branches)
    for (branch_name, commit) in branches.items():
        log('%s @%s' % (branch_name, commit))

    # collect commits
    commits = {}
    pattern = re.compile(r'^\[(\d+)\|\|(.*)\|\|(.*)\|\|\s?(.*)\]\s([0-9a-f]*)\s?([0-9a-f]*)\s?([0-9a-f]*)$')
    for start_point in set(branches.values()):
        cmd = 'git log --pretty=format:"[%%ct||%%cn||%%s||%%d] %%h %%p" -n %d %s' % (args.back, start_point)
        for line in get_output_lines(cmd):
            m = re.match(pattern, line)
            if not m:
                breakpoint()
            hash_ = m.group(5)
            if hash_ in commits:
                continue
            parent_hashes = [x for x in [m.group(6), m.group(7)] if x]
            entry = {'type':'normal', 'hash':hash_, 'date':m.group(1), 'author':m.group(2), 'message':m.group(3),
                        'ref_names':m.group(4), 'hash':hash_, 'parent_hashes':parent_hashes}
            commits[hash_] = entry

    # add placeholder commits for missing parents
    new_commits = {}
    for commit in commits.values():
        for h in commit['parent_hashes']:
            if h in commits:
                continue
            new_commits[h] = {'type':'absent_parent', 'hash':h}
    commits.update(new_commits)

    # convert commits to a networkx graph
    DG = nx.DiGraph()
    for commit in commits.values():
        DG.add_node(commit['hash'])
    for commit in commits.values():
        if commit['type'] == 'normal':
            for h in commit['parent_hashes']:
                DG.add_edge(commit['hash'], h)

    # process graph

    # draw graph
    print('digraph DG {')
    print('\trankdir="RL"')
    print('\t// nodes')
    for node in DG.nodes:
        # process commits as nodes
        if node in commits:
            commit = commits[node]
            lines = []

            if commit['type'] == 'normal':
                if not args.disclude_hash:
                    lines.append(commit['hash'])
                if not args.disclude_message:
                    message_prepared = commit['message']
                    if len(message_prepared) > args.message_length:
                        message_prepared = message_prepared[0:args.message_length] + '...'
                    message_prepared = message_prepared.replace('"', '\\"')
                    lines.append(message_prepared)
                print('\t"%s" [style=filled,fillcolor=lightyellow,shape=box,label="%s"];' % (node, '\\n'.join(lines)))
            elif commit['type'] == 'absent_parent':
                print('\t"%s" [style=filled,fillcolor=lightyellow,shape=box,label="..."];' % (node))
    for branch_name in branches:
        color = 'green' if 'HEAD' in branch_name else 'orange'
        print('\t"%s" [style=filled,fillcolor=%s];' % (branch_name, color))
        
    print('\t// edges')
    for edge in DG.edges():
        print('\t"%s" -> "%s";' % (edge[0], edge[1]))
    for (branch_name, hash_) in branches.items():
        print('\t"%s" -> "%s";' % (branch_name, hash_))
    print('}')
        
