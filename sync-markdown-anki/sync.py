#!/usr/bin/env python

import os
import re
import sys
import random

import commonmark

from helpers import *

DECK_NAME = 'test'

(RED, GREEN, YELLOW, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[33m', '\x1B[0m')

if __name__ == '__main__':
    command = None
    if sys.argv[1:]:
        command = sys.argv[1]

    fpath = 'Information.md'

    parser = commonmark.Parser()
    ast = parser.parse(open(fpath).read())

    # get rid of note ID's
    if command in ['reset', 'restart', 'clear']:
        mdf = MarkdownFileWithCards(fpath)
        mdf.clear_note_ids()
        mdf.save()

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
        mdf = MarkdownFileWithCards(fpath)
        changes_made = mdf.process_cards(DECK_NAME)
        if changes_made:
            mdf.save()
