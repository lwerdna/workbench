#!/usr/bin/env python

import os, sys, re, pprint, subprocess
import argparse
import subprocess

import networkx as nx

DEBUG=False

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
        elif ' detached at ' in line:
            # eg:
            # "(HEAD detached at 9a5099f) 9a5099f some commit message"
            m = re.match('^\s*\((.*) detached at [^\)]+\)\s+([^\s]+)\s+(.*)$', line)
            (branch_name, commit, descr) = m.group(1,2,3)
            if branch_name == 'HEAD':
                assert marked_head
            branches[branch_name] = commit
        else:
            # eg:
            # "  branch_name                    d5f7dc1 some commit message"
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
    parser.add_argument("--message", dest="include_message", action='store_true', help="include commit message")
    parser.add_argument("--no-message", dest="include_message", action='store_false', help="don't include commit message")
    parser.set_defaults(include_message=True)
    parser.add_argument("--hash", dest="include_hash", action='store_false', help="include commit hash")
    parser.add_argument("--no-hash", dest="include_hash", action='store_false', help="don't include commit hash")
    parser.set_defaults(include_hash=True)
    parser.add_argument("--author", dest="include_author", action='store_true', help="include author in nodes")
    parser.add_argument("--no-author", dest="include_author", action='store_true', help="don't include author in nodes")
    parser.set_defaults(include_author=False)
    parser.add_argument("--remote-branches", dest="remote_branches", action='store_true', help="include remote branches")
    parser.add_argument("--no-remote-branches", dest="remote_branches", action='store_true', help="don't include remote branches")
    parser.set_defaults(remote_branches=False)
    parser.add_argument("--message-length", dest="message_length", type=int, default=24, help="how many characters of commit message to include")
    parser.add_argument("--collapse", dest="collapse_threshold", type=int, default=8, help="length needed for linear run of commits to be collapsed (0 for no collapse)")
    parser.add_argument("--direction", default='vertical', choices=['horizontal', 'vertical'], help="layout direction")
    parser.add_argument("-b", "--back", type=int, default=16, help="how many commits back from each ref (0 for no limit)")
    parser.add_argument("--debug", dest="debug", action='store_true', help="print debugging messages as DOT comments")
    args = parser.parse_args()

    log('settings:')
    log('include message from nodes? %s' % args.include_message)
    log('include hash from nodes? %s' % args.include_hash)
    log('include author in nodes? %s' % args.include_author)
    log('include remote branches? %s' % args.remote_branches)
    log('message length in each node: %d' % args.message_length)
    log('collapse threshold: %d' % args.collapse_threshold)
    log('layout direction: %s' % args.direction)
    log('commits from each reference: %d' % args.back)
    log('debug messages? %s' % args.debug)

    DEBUG=args.debug

    branches = get_branches(args.remote_branches)
    for (branch_name, commit) in branches.items():
        log('%s @%s' % (branch_name, commit))

    # collect commits
    commits = {}
    pattern = re.compile(r'^\[(\d+)\|\|(.*)\|\|(.*)\|\|\s?(.*)\]\s([0-9a-f]*)\s?(.*)$')
    for start_point in set(branches.values()):
        limiter = '' if args.back==0 else ' -n %d'%args.back
        cmd = 'git log --pretty=format:"[%%ct||%%cn||%%s||%%d] %%h %%p"%s %s' % (limiter, start_point)
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

    # remove linear runs of commits
    if args.collapse_threshold != 0:
        seen = set()
        runs = []
        queue = ['branch:%s'%name for name in branches]
        while queue:
            cur = queue.pop()
            if cur in seen:
                continue
            seen.add(cur)
            run = []
            while(cur):
                run.append(cur)
                parents = list(DG.successors(cur))
                children = list(DG.predecessors(cur))
                if len(parents) == 1 and len(children) <= 1:
                    cur = parents[0]
                    continue
                queue.extend(parents)
                break
            runs.append(run)
        log('detected %d runs' % len(runs))
        for run in runs:
            log('\trun starting at %s is %d long' % (run[0], len(run)))

        #for run in sorted(runs, key=lambda x: len(x), reverse=True):
        for run in runs:
            if len(run) < args.collapse_threshold:
                log('run starting at %s was too short' % run[0])
                continue

            log('\t' + ','.join(run))

            # run[0]->run[1]->run[2]-> ... ->run[-3]->run[-2]->run[-1]
            for i in range(3, len(run)-3):
                log('\tremoving %s' % run[i])
                DG.remove_node(run[i])

            node = 'collapsed:%s ... %s' % (run[3], run[-4])

            DG.add_node(node)
            DG.add_edge(run[2], node)
            DG.add_edge(node, run[-3])

    # draw graph
    print('digraph DG {')
    if args.direction == 'horizontal':
        print('\trankdir="RL"')
    elif args.direction == 'vertical':
        print('\trankdir="TB"')
    # nodes
    print('\t// nodes')
    for node in DG.nodes:
        label_lines = []
        attribs = []

        if node.startswith('commit:'):
            attribs.append('style=filled')
            attribs.append('shape=box')

            info = commits[node[7:]]

            if args.include_hash:
                label_lines.append(info['hash'])
            if args.include_author:
                label_lines.append('(%s)' % info['author'])
            if args.include_message:
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
            attribs.append('shape=plaintext')
            label_lines.append('...')

        elif node.startswith('collapsed:'):
            attribs.append('style=filled')
            attribs.append('shape=box')
            attribs.append('fillcolor=cornsilk')
            label_lines.append('...')

        elif node.startswith('branch:'):
            branch_name = node[7:]
            color = 'green' if 'HEAD' in branch_name else 'orange'
            attribs.append('style=filled')
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

