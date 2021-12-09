# graph class hierarchy of low, medium, high LLIL instruction classes

# sys.path.append(os.path.join(os.environ['HOME'], 'repos', 'lwerdna', 'workbench', 'binja_misc')
# import graph_hlil_classes
# graph_hlil_classes.go(highlevelil.ILInstruction)
# graph_hlil_classes.go(mediumlevelil.ILInstruction)

# develop, then:
# import importlib; importlib.reload(graph_hlil_classes); graph_hlil_classes.go(ILInstruction)

# ...
# HighLevelILOperation.HLIL_FCMP_LT: 99 -> <class 'binaryninja.highlevelil.HighLevelILFcmpLt'>
# HighLevelILOperation.HLIL_FCMP_LE: 100 -> <class 'binaryninja.highlevelil.HighLevelILFcmpLe'>
# HighLevelILOperation.HLIL_FCMP_GE: 101 -> <class 'binaryninja.highlevelil.HighLevelILFcmpGe'>
# ...

import os, re

edges = None

def strip_class(foo):
    return re.match(r'^<class \'binaryninja\.(.*)\'>$', foo).group(1)

def crawl(foo):
    dst = strip_class(str(foo))
    for base in foo.__bases__:
        if base == object:
            continue

        src = strip_class(str(base))

        edges.add('"%s" -> "%s";\n' % (src, dst))
        crawl(base)

# prefer the commonil... parent
def crawl_common(foo):
    common_present = False
    for b in foo.__bases__:
        if 'commonil.' in str(b):
            common_present = True
            break

    dst = strip_class(str(foo))
    for base in foo.__bases__:
        if base == object:
            continue

        if common_present and not 'commonil.' in str(base):
            continue

        src = strip_class(str(base))

        edges.add('"%s" -> "%s";\n' % (src, dst))
        crawl(base)

def go(lookup):
    global edges
    edges = set()

    for c in lookup.values():
        crawl(c)

    draw()

def go_common(lookup):
    global edges
    edges = set()

    for c in lookup.values():
        crawl_common(c)

    draw()

def draw():
    global edges

    with open('/tmp/tmp.dot', 'w') as fp:
        fp.write('digraph g {\n')
        for edge in edges:
            fp.write(edge)
        fp.write('}\n')
    os.system('sfdp /tmp/tmp.dot -Tsvg -o /tmp/tmp.svg')
