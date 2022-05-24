#!/usr/bin/env python

# From a binary and function, produce a:
#  - svg for that function
#  - json with layout information in the svg

# example usage:
# $ bin2layout.py /path/to/tests _print_2path

# from binaryninja import *
import os
import webbrowser
import time
import sys
from pathlib import Path
from urllib.request import pathname2url

import binaryninja
from binaryninja.interaction import get_save_filename_input, show_message_box, TextLineField, ChoiceField, SaveFileNameField, get_form_input
from binaryninja.settings import Settings
from binaryninja.enums import MessageBoxButtonSet, MessageBoxIcon, MessageBoxButtonResult, InstructionTextTokenType, BranchType, DisassemblyOption, FunctionGraphType
from binaryninja.function import DisassemblySettings
from binaryninja.plugin import PluginCommand

colors = {
  'green': [162, 217, 175], 'red': [222, 143, 151], 'blue': [128, 198, 233], 'cyan': [142, 230, 237],
  'lightCyan': [176, 221, 228], 'orange': [237, 189, 129], 'yellow': [237, 223, 179], 'magenta': [218, 196, 209],
  'none': [74, 74, 74], 'disabled': [144, 144, 144]
}

escape_table = {"'": "&#39;", ">": "&#62;", "<": "&#60;", '"': "&#34;", ' ': "&#160;"}


def escape(toescape):
    # handle extended unicode
    toescape = toescape.encode('ascii', 'xmlcharrefreplace')
    # still escape the basics
    return ''.join(escape_table.get(chr(i), chr(i)) for i in toescape)

def instruction_data_flow(function, address):
    # TODO:  Extract data flow information
    length = function.view.get_instruction_length(address)
    func_bytes = function.view.read(address, length)
    hex = func_bytes.hex()
    padded = ' '.join([hex[i:i + 2] for i in range(0, len(hex), 2)])
    return 'Opcode: {bytes}'.format(bytes=padded)

def render_svg(function, form, showOpcodes, showAddresses):
    layout = {'blocks':[], 'edges':[]}

    settings = DisassemblySettings()
    if showOpcodes:
        settings.set_option(DisassemblyOption.ShowOpcode, True)
    if showAddresses:
        settings.set_option(DisassemblyOption.ShowAddress, True)
    if form == "LLIL":
        graph_type = FunctionGraphType.LowLevelILFunctionGraph
    elif form == "LLIL SSA":
        graph_type = FunctionGraphType.LowLevelILSSAFormFunctionGraph
    elif form == "Lifted IL":
        graph_type = FunctionGraphType.LiftedILFunctionGraph
    elif form == "Mapped Medium":
        graph_type = FunctionGraphType.MappedMediumLevelILFunctionGraph
    elif form == "Mapped Medium SSA":
        graph_type = FunctionGraphType.MappedMediumLevelILSSAFormFunctionGraph
    elif form == "MLIL":
        graph_type = FunctionGraphType.MediumLevelILFunctionGraph
    elif form == "MLIL SSA":
        graph_type = FunctionGraphType.MediumLevelILSSAFormFunctionGraph
    elif form == "HLIL":
        graph_type = FunctionGraphType.HighLevelILFunctionGraph
    elif form == "HLIL SSA":
        graph_type = FunctionGraphType.HighLevelILSSAFormFunctionGraph
    elif form == 'DISASM':
        graph_type = FunctionGraphType.NormalFunctionGraph
    else:
        assert False
    graph = function.create_graph(graph_type=graph_type, settings=settings)
    graph.layout_and_wait()
    heightconst = 15
    ratio = 0.48
    widthconst = heightconst * ratio

    output = ''
    output += '''<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" width="{width}" height="{height}">
        <defs>
            <marker id="arrow-TrueBranch" class="arrow TrueBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
                <path d="M 0 0 L 10 5 L 0 10 z" />
            </marker>
            <marker id="arrow-FalseBranch" class="arrow FalseBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
                <path d="M 0 0 L 10 5 L 0 10 z" />
            </marker>
            <marker id="arrow-UnconditionalBranch" class="arrow UnconditionalBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
                <path d="M 0 0 L 10 5 L 0 10 z" />
            </marker>
            <marker id="arrow-IndirectBranch" class="arrow IndirectBranch" viewBox="0 0 10 10" refX="10" refY="5" markerUnits="strokeWidth" markerWidth="8" markerHeight="6" orient="auto">
                <path d="M 0 0 L 10 5 L 0 10 z" />
            </marker>
        </defs>
    '''.format(width=graph.width * widthconst + 20, height=graph.height * heightconst + 20)

    layout['width'] = graph.width * widthconst + 20
    layout['height'] = graph.height * heightconst + 20

    output += '''    <g id="functiongraph0" class="functiongraph">
            <title>Function Graph 0</title>
    '''
    edges = ''
    for i, block in enumerate(graph):

        # Calculate basic block location and coordinates
        x = ((block.x) * widthconst)
        y = ((block.y) * heightconst)
        width = ((block.width) * widthconst)
        height = ((block.height) * heightconst)

        if i >= len(layout['blocks']):
            layout['blocks'].append(None)

        # Render block
        output += '        <g id="basicblock{i}" class="bb">\n'.format(i=i)
        output += '            <title>Basic Block {i}</title>\n'.format(i=i)
        rgb = colors['none']
        try:
            bb = block.basic_block
            if hasattr(bb.highlight, 'color'):
                color_code = bb.highlight.color
                color_str = bb.highlight._standard_color_to_str(color_code)
                if color_str in colors:
                    rgb = colors[color_str]
            else:
                rgb = [bb.highlight.red, bb.highlight.green, bb.highlight.blue]
        except:
            pass
        output += '            <rect class="basicblock" x="{x}" y="{y}" fill-opacity="0.4" height="{height}" width="{width}" fill="rgb({r},{g},{b})"/>\n'.format(
          x=x, y=y, width=width + 16, height=height + 12, r=rgb[0], g=rgb[1], b=rgb[2]
        )

        layout['blocks'][i] = { 'rect': [round(x,4), round(y,4), round(width+16,4), round(height+12,4)], 'targets':[]}


        # Render instructions, unfortunately tspans don't allow copying/pasting more
        # than one line at a time, need SVG 1.2 textarea tags for that it looks like

        output += '            <text x="{x}" y="{y}">\n'.format(x=x, y=y + (i+1) * heightconst)
        for line_i, line in enumerate(block.lines):
            output += '                <tspan id="instr-{address}" x="{x}" y="{y}">'.format(
              x=x + 6, y=y + 6 + (line_i+0.7) * heightconst, address=hex(line.address)[:-1]
            )
            hover = instruction_data_flow(function, line.address)
            output += '<title>{hover}</title>'.format(hover=hover)
            for token in line.tokens:
                # TODO: add hover for hex, function, and reg tokens
                output += '<tspan class="{tokentype}">{text}</tspan>'.format(
                  text=escape(token.text), tokentype=InstructionTextTokenType(token.type).name
                )
            output += '</tspan>\n'
        output += '            </text>\n'
        output += '        </g>\n'

        # Edges are rendered in a seperate chunk so they have priority over the
        # basic blocks or else they'd render below them

        for edge in block.outgoing_edges:
            points = ""
            x, y = edge.points[0]
            points += str(x * widthconst) + "," + \
                      str(y * heightconst + 12) + " "
            for x, y in edge.points[1:-1]:
                points += str(x * widthconst) + "," + \
                          str(y * heightconst) + " "
            x, y = edge.points[-1]
            points += str(x * widthconst) + "," + \
                      str(y * heightconst + 0) + " "
            if edge.back_edge:
                edges += '        <polyline class="edge-binja {type}" points="{points}" marker-end="url(#arrow-{type})"/>\n'.format(
                  type=BranchType(edge.type).name, points=points
                )
            else:
                edges += '        <polyline class="edge-binja {type}" points="{points}" marker-end="url(#arrow-{type})"/>\n'.format(
                  type=BranchType(edge.type).name, points=points
                )
            layout['blocks'][i]['targets'].append([int(edge.target.basic_block.index), edge.type.name])
            
            tmp = []
            for pair in points.strip().split(' '):
                (x,y) = pair.split(',')
                tmp += [round(float(x),4), round(float(y),4)]
            layout['edges'].append({'type':edge.type.name, 'format':'polyline', 'points':tmp})

    output += ' ' + edges + '\n'
    output += '    </g>\n'
    output += '</svg>'

    return output, layout


if __name__ == '__main__':
    fpath = sys.argv[1]
    fnames = []

    bview = binaryninja.open_view(fpath)

    funcs = []
    if sys.argv[2:]:
        funcs = bview.get_functions_by_name(sys.argv[2])
    else:
        funcs = list(bview.functions)

    count = 0
    for func in funcs:
        if len(func.basic_blocks) < 5 or len(func.basic_blocks) > 25:
            continue

        (svg, layout) = render_svg(func, 'DISASM', True, True)

        #tmp = fname + '_binja.svg'
        tmp = f'./datas/{func.name}.svg'
        print(f'writing {tmp}')
        with open(tmp, 'w') as fp:
            fp.write(svg)

        #tmp = fname + '_binja.json'
        tmp = f'./datas/{func.name}_binja.json'
        print(f'writing {tmp}')
        with open(tmp, 'w') as fp:
            import json
            fp.write(json.dumps(layout, indent=2))

        count += 1
        if count >= 100:
            break;
