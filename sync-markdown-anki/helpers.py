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

def render_markdown(node):
    children = list(collect_children(node))

    result = ''

    if node.t == 'document':
        for child in children:
            result += render_markdown(child)
    elif node.t == 'paragraph':
        for child in children:
            result += render_markdown(child)
    elif node.t == 'heading':
        result = '#'*node.level + ' ' + ''.join(render_markdown(c) for c in children) + '\n'
    elif node.t == 'text':
        result = node.literal
    elif node.t == 'code_block':
        if node.is_fenced:
            result = node.fence_char * node.fence_length + node.info + '\n'
            result += node.literal
            result += node.fence_char * node.fence_length
        else:
            result = '\n'.join(f'    {line}' for line in node.literal.split('\n'))
    elif node.t == 'softbreak':
        result += '\n'
    elif node.t == 'code':
        result = '`' + node.literal + '`'
    elif node.t == 'list':
        for child in children:
            result += render_markdown(child)
            result += '\n'
    elif node.t == 'item':
        if node.list_data['type'] == 'bullet':
            bullet = node.list_data['bullet_char']
        elif node.list_data['type'] == 'ordered':
            bullet = node.list_data['start']
        else:
            breakpoint()
            pass

        for child in children:
            result += f'{bullet} ' + render_markdown(child)

    elif node.t == 'link':
        assert len(children) == 1
        result = f'[{node.destination}]({render_markdown(node.first_child)})'
    elif node.t == 'emph':
        assert len(children) == 1
        result = '_' + render_markdown(node.first_child) + '_'
    elif node.t == 'strong':
        assert len(children) == 1
        result = '**' + render_markdown(node.first_child) + '**'
    elif node.t == 'html_inline':
        result = node.literal
    elif node.t == 'html_block':
        result = node.literal
    elif node.t == 'thematic_break':
        result = '---\n'
    else:
        print(f'unknown type: {node.t}')
        print(node.pretty())
        breakpoint()

    # decide whether to add space after this block
    end_n = False
    if node.t == 'heading':
        end_n = True
    elif node.t == 'code_block':
        end_n = True
    elif node.t == 'html_block':
        end_n = True
    elif node.t == 'paragraph':
        if node.parent.t == 'document':
            if node != node.parent.last_child:
                end_n = True
        else:
            if not list in [anc.t for anc in collect_ancestors(node)]:
                end_n = True

    if end_n:
        while not result.endswith('\n'):
            result = result + '\n'

    if node.last_line_blank:
        while not result.endswith('\n\n'):
            result = result + '\n'

    return result

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
