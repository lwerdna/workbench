#!/usr/bin/env python

import os
import sys
import json
import random
import urllib.request

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

#invoke('createDeck', deck='test')
if __name__ == '__main__':
    if sys.argv[1] == 'decks':
        #result = invoke('deckNames')
        result = invoke('deckNamesAndIds')

        for (deck_name, deck_id) in result.items():
            print(f'{deck_id}: {deck_name}')

    if sys.argv[1] == 'cards':
        deck_name = 'test'
        result = invoke('findCards', query='deck:'+deck_name)

        for card_id in result:
            print(card_id)

            result = invoke('cardsInfo', cards=[card_id])
            print(' fields: ' + str(result[0]['fields'].keys()))
            print('  Front: ' + result[0]['fields']['Front']['value'])
            print('   Back: ' + result[0]['fields']['Back']['value'])

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
        result = invoke('addNote', note=foo)
        print(result)
