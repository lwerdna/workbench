import json
import urllib.request

import commonmark

#------------------------------------------------------------------------------
# ANKICONNECT HELPERS
#------------------------------------------------------------------------------

def ankiconnect_request(action, **params):
    return {'action': action, 'params': params, 'version': 6}

def ankiconnect_invoke(action, **params):
    requestJson = json.dumps(ankiconnect_request(action, **params)).encode('utf-8')
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

#------------------------------------------------------------------------------
# COMMONMARK HELPERS
#------------------------------------------------------------------------------

def collect_children(node):
    current = node.first_child
    while current:
        yield current
        current = current.nxt

def collect_ancestors(node):
    current = node.parent
    while current:
        yield current
        current = current.parent

#------------------------------------------------------------------------------
# CARD GENERATION
#------------------------------------------------------------------------------

def add_note(deck_name, front, back):
    info = { 'deckName': deck_name,
             'modelName': 'Basic',
             'fields': {
               'Front': front,
               'Back': back 
             },
             "options":
             {
               "allowDuplicate": True,
               "duplicateScope": "deck",
               "duplicateScopeOptions":
               {
                 "deckName": deck_name,
                 "checkChildren": False,
                 "checkAllModels": False
               }
             }
           }

    note_id = ankiconnect_invoke('addNote', note=info)
    return note_id

def render_to_anki_html(ast_node):
    renderer = commonmark.HtmlRenderer()
    html = renderer.render(ast_node).strip()
    return html
