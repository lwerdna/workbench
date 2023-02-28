#!/usr/bin/env python

import os
import sys
import base64
import random
import pprint

import helpers

#helpers.ankiconnect_invoke('createDeck', deck='test')
if __name__ == '__main__':
    #--------------------------------------------------------------------------
    # collection-wide commands
    #--------------------------------------------------------------------------
    # LIST ALL DECKS
    if sys.argv[1] == 'decks':
        #result = helpers.ankiconnect_invoke('deckNames')
        result = helpers.ankiconnect_invoke('deckNamesAndIds')

        for (deck_name, deck_id) in result.items():
            print(f'{deck_id}: {deck_name}')

        sys.exit(0)

    # LIST MEDIA FILE NAMES
    if sys.argv[1] in ['listmedia', 'media']:
        result = helpers.ankiconnect_invoke('getMediaFilesNames', pattern='minima maxima calculus.png')
        print('\n'.join(result))
        sys.exit(0)

    # ACTUALLY RETRIEVE MEDIA
    if sys.argv[1] in ['getmedia', 'retrievemedia']:
        for fname in helpers.ankiconnect_invoke('getMediaFilesNames'):
            fpath = os.path.join('.', 'media', fname)

            print(f'retrieving {fname} -> {fpath}')
            b64 = helpers.ankiconnect_invoke('retrieveMediaFile', filename=fname)

            with open(fpath, 'wb') as fp:
                fp.write(base64.b64decode(b64))
        sys.exit(0)

    #--------------------------------------------------------------------------
    # deck-specific commands
    #--------------------------------------------------------------------------
    deck_name, command = sys.argv[1:]

    if command == 'cards':
        result = helpers.ankiconnect_invoke('findCards', query='deck:'+deck_name)

        for card_id in result:
            print('')
            print(card_id)
            print('----------------')

            result = helpers.ankiconnect_invoke('cardsInfo', cards=[card_id])
            assert len(result) == 1
            pprint.pprint(result[0])

    if command == 'notes':
        result = helpers.ankiconnect_invoke('findNotes', query='deck:'+deck_name)

        for note_id in result:
            print('')
            print(note_id)
            print('----------------')

            result = helpers.ankiconnect_invoke('notesInfo', notes=[note_id])
            assert len(result) == 1
            pprint.pprint(result[0])

    if command == 'addbasic':
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
