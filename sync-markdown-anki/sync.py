#!/usr/bin/env python

import os
import re
import sys
import random

import commonmark

from helpers import *

DECK_NAME = 'test'

(RED, GREEN, YELLOW, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[33m', '\x1B[0m')

def update_card(note_id, front_html, back_html):
    ninfo = ankiconnect_invoke('notesInfo', notes=[note_id])
    ninfo = ninfo[0]
    if ninfo == {}:
        print(RED + f'{note_id} not found, something\'s wrong' + NORMAL)
        sys.exit(-1)

    update = False

    front_ = ninfo['fields']['Front']['value']
    back_ = ninfo['fields']['Back']['value']
    if front_ != front_html or back_ != back_html:
        #breakpoint()
        #print(f' local front: {card["FRONT"]}')
        #print(f'remote front: {front_}')
        print(f'{YELLOW}updating {qdescr}{NORMAL}')

        ndata = {'id': ninfo['noteId'],
                 'fields': {
                        'Front': front_html,
                        'Back': back_html
                    }
                }
        ninfo = ankiconnect_invoke('updateNoteFields', note=ndata)
        print('result of updating: ' + str(ninfo))

def traverse_looking_for_cards(node):
    children = list(collect_children(node))

    if node.t == 'html_block':
        if node.literal.startswith('<!-- ANKI0 '):
            assert node.nxt
            front_md = render_markdown(node.nxt)
            front_md = process_typora_math(front_md)
            front = render_anki_html(front_md)

            assert node.nxt.nxt
            assert node.nxt.nxt.literal == '<!-- ANKI1 -->'

            assert node.nxt.nxt.nxt
            back_md = render_markdown(node.nxt.nxt.nxt)
            back_md = process_typora_math(back_md)
            back = render_anki_html(back_md)

            assert node.nxt.nxt.nxt.nxt
            assert node.nxt.nxt.nxt.nxt.literal == '<!-- ANKI2 -->'

            #if 'P(H)P(E|H)' in back:
            #    breakpoint()

        if re.match(r'^<!-- ANKI0 -->', node.literal):
            print('---- <NEW_CARD> ----')
            print(front)
            print('----')
            print(back)
            print('---- </NEW_CARD> ----')

            note_id = add_note(DECK_NAME, front, back)
            node.literal = f'<!-- ANKI0 NID:{note_id} -->'

        elif m := re.match(r'^<!-- ANKI0 NID:(\d+) -->$', node.literal):
            nid = int(m.group(1))
            update_card(nid, front, back)

    else:
        for child in children:
            traverse_looking_for_cards(child)

def traverse_clearing_nids(node):
    if node.t == 'html_block' and re.match(r'^<!-- ANKI0 NID:\d+ -->$', node.literal):
        print(f'clearing: {node.literal}')
        node.literal = '<!-- ANKI0 -->'
    else:
        for child in collect_children(node):
            traverse_clearing_nids(child)

if __name__ == '__main__':
    command = None
    if sys.argv[1:]:
        command = sys.argv[1]

    fname = 'Information.md'
    parser = commonmark.Parser()
    ast = parser.parse(open(fname).read())

    # get rid of note ID's
    if command in ['reset', 'restart', 'clear']:
        traverse_clearing_nids(ast)
        markdown = render_markdown(ast)
        with open(fname, 'w') as fp:
            fp.write(markdown)

    # render to HTML
    elif command == 'html':
        # this is how the ast would be used to generate HTML
        renderer = commonmark.HtmlRenderer()
        html = renderer.render(ast)
        print(html)

    # render back to markdown
    elif command == 'md':
        md = render_markdown(ast)
        print(md)

    # dump contents
    elif command == 'dump':
        #print(commonmark.dumpJSON(ast))
        #print(commonmark.dumpAST(ast))
        dump(ast)

    # markdown -> anki
    else:
        traverse_looking_for_cards(ast)
        markdown = render_markdown(ast)
        with open(fname, 'w') as fp:
            fp.write(markdown)
