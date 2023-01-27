#!/usr/bin/env python

import os
import sys
import base64
import random

import helpers

#helpers.ankiconnect_invoke('createDeck', deck='test')
if __name__ == '__main__':
    if sys.argv[1] == 'decks':
        #result = helpers.ankiconnect_invoke('deckNames')
        result = helpers.ankiconnect_invoke('deckNamesAndIds')

        for (deck_name, deck_id) in result.items():
            print(f'{deck_id}: {deck_name}')

    if sys.argv[1] == 'cards':
        deck_name = 'test'
        result = helpers.ankiconnect_invoke('findCards', query='deck:'+deck_name)

        for card_id in result:
            print(card_id)

            result = helpers.ankiconnect_invoke('cardsInfo', cards=[card_id])
            print(' fields: ' + str(result[0]['fields'].keys()))
            print('  Front: ' + result[0]['fields']['Front']['value'])
            print('   Back: ' + result[0]['fields']['Back']['value'])

    if sys.argv[1] == 'notes':
        deck_name = 'test'
        result = helpers.ankiconnect_invoke('findNotes', query='deck:'+deck_name)

        for note_id in result:
            print(note_id)

            result = helpers.ankiconnect_invoke('notesInfo', notes=[note_id])
            assert len(result) == 1
            for (fname, fdict) in result[0]['fields'].items():
                print(f'{fname}: {fdict["value"]}')

    if sys.argv[1] in ['listmedia', 'media']:
        deck_name = 'test'
        result = helpers.ankiconnect_invoke('getMediaFilesNames', pattern='*minima*')
        print('\n'.join(result))

    if sys.argv[1] in ['getmedia', 'retrievemedia']:
        deck_name = 'test'
        for fname in helpers.ankiconnect_invoke('getMediaFilesNames'):
            fpath = os.path.join('.', 'media', fname)

            print(f'retrieving {fname} -> {fpath}')
            b64 = helpers.ankiconnect_invoke('retrieveMediaFile', filename=fname)

            with open(fpath, 'wb') as fp:
                fp.write(base64.b64decode(b64))

    if sys.argv[1] == 'addbasic':
        deck_name = 'test'
        foo = { 'deckName': deck_name,
                'modelName': 'Basic',
                'fields': {
                    'Front': 'front content ' + str(random.random()),
                    'Back': 'YOMOMMA',
                    'MyCustomField': '2938758235'
                }
            }
        result = helpers.ankiconnect_invoke('addNote', note=foo)
        print(result)
