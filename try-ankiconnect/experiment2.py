#!/usr/bin/env python

import os
import re
import sys
import json
import random
import urllib.request

DECK_NAME = 'test'

(RED, GREEN, YELLOW, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[33m', '\x1B[0m')

def request(action, **params):
    return {'action': action, 'params': params, 'version': 6}

def invoke(action, **params):
    requestJson = json.dumps(request(action, **params)).encode('utf-8')
    response = json.load(urllib.request.urlopen(urllib.request.Request('http://localhost:8765', requestJson)))
    if len(response) != 2:
        raise Exception('response has an unexpected number of fields')
    if 'error' not in response:
        raise Exception('response is missing required error field')
    if 'result' not in response:
        raise Exception('response is missing required result field')
    if response['error'] is not None:
        raise Exception(response['error'])
    return response['result']

class MarkdownWithAnkiFences(object):
    def __init__(self, fpath):
        self.fpath = fpath
        self.elements = []
        self.parse()

    # convert the contents (lines) of an anki-fenced code block to a dictionary, eg:
    #
    # ```anki
    # FRONT: What's the first animal?
    # BACK: Aardvark
    # NID: 12345678
    # ```
    #
    # is parsed into a list of lines:
    #
    # [
    #   "FRONT: What's the first animal?",
    #   "BACK: Aardvark",
    #   "NID: 12345678"
    # ]
    #
    # then to:
    #
    # {'front':'What\'s the first animal?', 'back':'Aaardvark', 'nid':12345678}
    def parse_anki_fence(self, lines):
        front_i, back_i, note_id_i = None, None, None
        for (i, line) in enumerate(lines):
            if line.startswith('FRONT: '):
                front_i = i
            elif line.startswith('BACK: '):
                back_i = i
            elif line.startswith('NID: '):
                note_id_i = i

        if front_i == None:
            raise Exception('parsing card: couldn\'t find FRONT:')
        if back_i == None:
            raise Exception('parsing card: couldn\'t find BACK:')

        if note_id_i == None:
            if not (front_i < back_i):
                raise Exception('expected FRONT:, BACK: in order')
        else:
            if not (front_i < back_i < note_id_i):
                raise Exception('expected FRONT:, BACK:, NID: in order')

        front = ''.join(lines[front_i: back_i])
        assert front.startswith('FRONT: ')
        front = front[7:].strip()

        end = note_id_i if note_id_i != None else len(lines)+1
        back = ''.join(lines[back_i: end])
        assert back.startswith('BACK: ')
        back = back[6:].strip()

        nid = None
        if note_id_i != None:
            if note_id_i != len(lines)-1:
                raise Exception('expected NID: on last line of fenced anki')
            m = re.match(r'^NID: (\d+)$', lines[note_id_i])
            if not m:
                raise Exception('malformed card id')
            nid = int(m.group(1))

        return {'FRONT':front, 'BACK':back, 'NID':nid}

    def parse(self):
        with open(self.fpath) as fp:
            lines = fp.readlines()

        lines_block = []
        lines_card = []

        STATE = 'start'
        for (i,line) in enumerate(lines):
            match STATE:
                case 'start':
                    if line == '```anki\n':
                        #print(f'{i}: (START) -> CARD')
                        STATE = 'card'
                    else:
                        #print(f'{i}: (START) -> BLOCK')
                        STATE = 'block'
                        lines_block = [line]
                case 'block':
                    if line == '```anki\n':
                        if lines_block:
                            #print(f'{i}: (BLOCK) closing')
                            self.elements.append(lines_block)
                            lines_block = []
                        #print(f'{i}: (BLOCK) -> CARD')
                        STATE = 'card'
                    elif i == len(lines) - 1:
                        lines_block.append(line)
                        #print(f'{i}: (BLOCK) closing')
                        self.elements.append(lines_block)
                        lines_block = []
                    else:
                        lines_block.append(line)
                case 'card':
                    if line in ['```', '```\n']:
                        #print(f'{i}: (CARD) closing')
                        assert lines_card
                        self.elements.append(self.parse_anki_fence(lines_card))
                        lines_card = []
                        #print(f'{i}: (CARD) -> BLOCK')
                        STATE = 'block'
                    else:
                        lines_card.append(line)
                case _:
                    assert False

    def update_card(self, card):
        self.elements[card['index']] = card

    def cards(self):
        for (i, elem) in enumerate(self.elements):
            if type(elem) == dict:
                result = dict(elem)
                result['index'] = i
                yield result

    def __str__(self):
        result = []

        #for elem in self.elements:
        #    if type(elem) == list:
        #        result.append(f'block with {len(elem)} lines')
        #    elif type(elem) == dict:
        #        result.append(f'card')

        for elem in self.elements:
            if type(elem) == list:
                result.extend(elem)
            elif type(elem) == dict:
                result.append(f'```anki\n')
                result.append(f'FRONT: {elem["FRONT"]}\n')
                result.append(f'BACK: {elem["BACK"]}\n')
                if elem.get('NID'):
                    result.append(f'NID: {elem["NID"]}\n')
                result.append(f'```\n')

        return ''.join(result)

    def save(self):
        with open(self.fpath, 'w') as fp:
            fp.write(str(self))

if __name__ == '__main__':
    files = [f for f in os.listdir('.') if f.endswith('.md')]
    if sys.argv[1:]:
        files = [sys.argv[1]]

    for fname in files:
        #print('opening: ' + fname)
        contents = open(fname).read()

        if not '```anki' in contents:
            #print('no cards, skipping')
            continue

        md = MarkdownWithAnkiFences(fname)

        for card in md.cards():
            # quick description
            qdescr = card['FRONT']
            if len(qdescr) > 64:
                qdescr = qdescr[0:64] + '...'
            nid = card.get('NID')
            if nid:
                qdescr += f' (ID:{nid})'

            # ID ALREADY ASSIGNED? POSSIBLY UPDATE CARD
            if card.get('NID'):
                note_id = card['NID']

                ninfo = invoke('notesInfo', notes=[note_id])
                ninfo = ninfo[0]
                if ninfo == {}:
                    print(RED + f'{qdescr} not found, something\'s wrong' + NORMAL)
                    sys.exit(-1)

                update = False

                front_ = ninfo['fields']['Front']['value']
                back_ = ninfo['fields']['Back']['value']
                if front_ != card['FRONT'] or back_ != card['BACK']:
                    #breakpoint()
                    #print(f' local front: {card["FRONT"]}')
                    #print(f'remote front: {front_}')
                    print(f'{YELLOW}updating {qdescr}{NORMAL}')

                    ndata = {'id': ninfo['noteId'],
                             'fields': {
                                    'Front': card['FRONT'],
                                    'Back': card['BACK']
                                }
                            }
                    ninfo = invoke('updateNoteFields', note=ndata)
                    print('result of updating: ' + str(ninfo))
            else:
                info = { 'deckName': DECK_NAME,
                         'modelName': 'Basic',
                         'fields': {
                           'Front': card['FRONT'],
                           'Back': card['BACK']
                         },
                         "options":
                         {
                           "allowDuplicate": True,
                           "duplicateScope": "deck",
                           "duplicateScopeOptions":
                           {
                             "deckName": DECK_NAME,
                             "checkChildren": False,
                             "checkAllModels": False
                           }
                         }
                       }

                note_id = invoke('addNote', note=info)

                card['NID'] = note_id
                md.update_card(card)
                print(GREEN + f'adding new note, id={note_id}' + NORMAL)

        md.save()

