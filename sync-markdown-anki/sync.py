#!/usr/bin/env python

import os
import re
import sys
import random

from helpers import *

DECK_NAME = 'test'
FPATH_MARKDOWN = 'Information.md'

(RED, GREEN, YELLOW, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[33m', '\x1B[0m')

if __name__ == '__main__':
    cmd = 'sync'
    if sys.argv[1:]:
        cmd = sys.argv[1]

    if cmd in ['sync', 'synchronize']:
        mdf = MarkdownFileWithAnki(FPATH_MARKDOWN)
        changes_made = mdf.process_notes(DECK_NAME)
        if changes_made:
            mdf.save()

    # get rid of note ID's
    elif cmd in ['reset', 'restart', 'clear']:
        mdf = MarkdownFileWithAnki(FPATH_MARKDOWN)
        mdf.clear_note_ids()
        mdf.save()

