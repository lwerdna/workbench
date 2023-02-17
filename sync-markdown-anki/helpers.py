import re
import sys
import json
import urllib.request

import commonmark

(RED, GREEN, YELLOW, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[33m', '\x1B[0m')

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

def dump(node, depth=0):
    indent = '  '*depth

    pos_str = ''
    if node.sourcepos:
        pos_str = f'{node.sourcepos[0][0]},{node.sourcepos[0][1]}-{node.sourcepos[1][0]},{node.sourcepos[1][1]}'

    extra = ''
    if node.t == 'text':
        extra = node.literal
        if len(extra) > 32:
            extra = extra[0:32] + '...'
        extra = f' "{extra}"'

    print(f'{indent}{node.t} {pos_str}{extra} llb:{node.last_line_blank}')

    for child in collect_children(node):
        dump(child, depth+1)

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
            bullet = str(node.list_data['start']) + '.'
        else:
            breakpoint()
            pass

        for child in children:
            result += f'{bullet} ' + render_markdown(child)

    elif node.t == 'link':
        link_text = ''.join(render_markdown(c) for c in children)
        result = f'[{link_text}]({node.destination})'
    elif node.t == 'emph':
        result = '_' + ''.join(render_markdown(c) for c in children) + '_'
    elif node.t == 'strong':
        result = '**' + ''.join(render_markdown(c) for c in children) + '**'
    elif node.t == 'html_inline':
        result = node.literal
    elif node.t == 'html_block':
        result = node.literal
    elif node.t == 'thematic_break':
        result = '---\n'
    elif node.t == 'block_quote':
        for child in children:
            result += '> ' + render_markdown(child)
    elif node.t == 'image':
        return f'![]({node.destination})'
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
            if not 'list' in [anc.t for anc in collect_ancestors(node)]:
                end_n = True

    if end_n:
        while not result.endswith('\n'):
            result = result + '\n'

    if node.last_line_blank:
        while not result.endswith('\n\n'):
            result = result + '\n'

    return result

#------------------------------------------------------------------------------
# CARD RENDERING
#------------------------------------------------------------------------------

def process_math_stage0(markdown):
    lines = []
    in_block = False

    for l in markdown.split('\n'):
        # handle double dollar separately
        if l == '$$':
            lines.append('</math_block>' if in_block else '<math_block>')
            in_block = not in_block
            continue

        if '$' in l:
            chars = list(l)
            toggle = False
            for i in range(len(chars)):
                if chars[i] == '$':
                    chars[i] = '</math_inline>' if toggle else '<math_inline>'
                    toggle = not toggle
            lines.append(''.join(chars))
            continue

        lines.append(l + '\n')

    return ''.join(lines)

def process_math_stage1(html):
    html = html.replace('&lt;math_block&gt;', r'\[')
    html = html.replace('&lt;/math_block&gt;', r'\]')
    html = html.replace('&lt;math_inline&gt;', r'\(')
    html = html.replace('&lt;/math_inline&gt;', r'\)')
    return html

def render_anki_html(x):
    if type(x) == str:
        ast_node = commonmark.Parser().parse(x)
    else:
        ast_node = x
    renderer = commonmark.HtmlRenderer({'softbreak': '<br />'})
    html = renderer.render(ast_node).strip()
    return html

#------------------------------------------------------------------------------
# CONVENIENCE CARD ADD/UPDATE
#------------------------------------------------------------------------------

def add_note(deck_name, data0, data1):
    if '{{c1::' in data0:
        modelName = 'Cloze'
        fields = { 'Text': data0, 'Extra': data1 }
    else:
        modelName = 'Basic'
        fields = { 'Front': data0, 'Back': data1 }

    info = { 'deckName': deck_name,
             'modelName': modelName,
             'fields': fields,
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

def update_note(note_id, info0_html, info1_html):
    ninfo = ankiconnect_invoke('notesInfo', notes=[note_id])

    assert len(ninfo) == 1
    ninfo = ninfo[0]
    if ninfo == {}:
        print(RED + f'NOTE ID: {note_id} not found, something\'s wrong' + NORMAL)
        sys.exit(-1)

    match ninfo['modelName']:
        case 'Basic':
            field0, field1 = 'Front', 'Back'
        case 'Cloze':
            field0, field1 = 'Text', 'Extra'
        case _:
            raise Exception(f'unknown note model: {_}')

    info0 = ninfo['fields'][field0]['value']
    info1 = ninfo['fields'][field1]['value']

    if info0 != info0_html or info1 != info1_html:
        print(f'{YELLOW}updating {note_id}{NORMAL}')

        ndata = {'id': ninfo['noteId'],
                 'fields': {field0: info0_html, field1: info1_html}
                }
        ninfo = ankiconnect_invoke('updateNoteFields', note=ndata)
        if ninfo:
            print('result of updating: ' + str(ninfo))

def get_deck_note_ids(deck_name):
    return ankiconnect_invoke('findNotes', query='deck:'+deck_name)

#------------------------------------------------------------------------------
# PARSING
#------------------------------------------------------------------------------

class MarkdownFileWithAnki(object):
    def __init__(self, fpath):
        with open(fpath) as fp:
            self.lines = fp.readlines()

        self.fpath = fpath

        # parse card fences
        self.cards = []
        mark0, mark1, mark2, state = 0, 0, 0, 0
        for i,line in enumerate(self.lines):
            if line.startswith('<!-- ANKI0 '):
                assert state == 0
                mark0, state = i, 1
            if line.startswith('<!-- ANKI1 '):
                assert state == 1
                mark1, state = i, 2
            if line.startswith('<!-- ANKI2 '):
                assert state == 2
                mark2, state = i, 3
                self.cards.append((mark0, mark1, mark2))
                mark0 = mark1 = mark2 = state = 0

    def clear_note_ids(self):
        for a,b,c in self.cards:
            if m := re.match(r'^<!-- ANKI0 NID:(\d+) -->\n$', self.lines[a]):
                self.lines[a] = '<!-- ANKI0 -->\n'

    def get_note_ids(self):
        result = set()
        for a,b,c in self.cards:
            if m := re.match(r'^<!-- ANKI0 NID:(\d+) -->\n$', self.lines[a]):
                result.add(int(m.group(1)))
        return result

    def process_notes(self, destination_deck):
        changes_made = False

        for a,b,c in self.cards:
            info0_md = ''.join(self.lines[a+1:b])
            info1_md = ''.join(self.lines[b+1:c])

            info0_md = process_math_stage0(info0_md)
            info0_html = render_anki_html(info0_md)
            info0_html = process_math_stage1(info0_html)

            info1_md = process_math_stage0(info1_md)
            info1_html = render_anki_html(info1_md)
            info1_html = process_math_stage1(info1_html)

            if self.lines[a] == '<!-- ANKI0 -->\n':
                note_id = add_note(destination_deck, info0_html, info1_html)
                self.lines[a] = f'<!-- ANKI0 NID:{note_id} -->\n'
                changes_made = True
            elif m := re.match(r'^<!-- ANKI0 NID:(\d+) -->\n$', self.lines[a]):
                note_id = int(m.group(1))
                update_note(note_id, info0_html, info1_html)
            else:
                raise Exception(f'malformed ANKI fence: {self.lines[a]}')

        return changes_made

    def save(self):
        with open(self.fpath, 'w') as fp:
            fp.write(''.join(self.lines))

    def __str__(self):
        lines = []
        lines.append(f'MarkdownFile "{self.fpath}" with {len(self.cards)} cards:')
        for i, (a,b,c) in enumerate(self.cards):
            lines.append(f'card {i} with fences at lines {a+1}, {b+1}, {c+1}')
        return '\n'.join(lines)

#------------------------------------------------------------------------------
# MARKDOWN AST TRAVERSERS (obsolete)
#------------------------------------------------------------------------------

def traverse_looking_for_cards(node, deck_name):
    children = list(collect_children(node))

    if node.t == 'html_block':
        if node.literal.startswith('<!-- ANKI0 '):
            front, back = '', ''

            # search for ANKI1
            node1 = node.nxt
            while node1.literal != '<!-- ANKI1 -->':
                md = render_markdown(node1)
                md = process_math_stage0(md)
                front += render_anki_html(md)
                node1 = node1.nxt

            # search for ANKI2
            node2 = node1.nxt
            while node2.literal != '<!-- ANKI2 -->':
                md = render_markdown(node2)
                md = process_math_stage0(md)
                back += render_anki_html(md)
                node2 = node2.nxt

        if re.match(r'^<!-- ANKI0 -->', node.literal):
            print('---- <NEW_CARD> ----')
            print(front)
            print('----')
            print(back)
            print('---- </NEW_CARD> ----')

            note_id = add_note(deck_name, front, back)
            node.literal = f'<!-- ANKI0 NID:{note_id} -->'

        elif m := re.match(r'^<!-- ANKI0 NID:(\d+) -->$', node.literal):
            nid = int(m.group(1))
            update_note(nid, front, back)

    else:
        for child in children:
            traverse_looking_for_cards(child, deck_name)

def traverse_clearing_nids(node):
    if node.t == 'html_block' and re.match(r'^<!-- ANKI0 NID:\d+ -->$', node.literal):
        print(f'clearing: {node.literal}')
        node.literal = '<!-- ANKI0 -->'
    else:
        for child in collect_children(node):
            traverse_clearing_nids(child)

