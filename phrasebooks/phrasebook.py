import os
fpath = os.path.join(os.environ['HOME'], 'Desktop', 'TA1 Output', 'TA1-Kudu-traces', 'CVE-2019-10999_dcs-5020l_v1.15.12_semantics.jsonl')

f'f-strings'
r'raw-strings'
b'byte-strings'

# structural pattern matching
match command.split():
    case ["quit"]:
        print("Goodbye!")
        quit_game()
    case ["look"]:
        current_room.describe()
    case ["get", obj]:
        character.get(obj, current_room)
    case ["go", direction]:
        current_room = current_room.neighbor(direction)

###############################################################################
## debugging help stuff
###############################################################################
# drop into repl
def interact():
    import code
    code.InteractiveConsole(locals=globals()).interact()
    
# print stack trace
import traceback
traceback.print_stack()

# run under debugger
python3 -m pdb myscript.py

# bring up pdb
breakpoint()
import inspect
import inspect.getfile(os)
# old way: import pdb; pdb.set_trace()

# print nicely
import pprint
pprint.pprint(foo)

def qt_breakpoint():
    '''Set a tracepoint in the Python debugger that works with Qt'''
    from pdb import set_trace
    from PyQt5.QtCore import pyqtRemoveInputHook
    pyqtRemoveInputHook()
    set_trace()

###############################################################################
## file system stuff
###############################################################################

pics = filter(lambda x: x.endswith('.jpg'), os.listdir('.'))

def dirtree(root):
    result = []
    for root, dirs, fnames in os.walk(root):
        for dir in dirs:
            #print os.path.join(root, dir)
            pass
        for fname in fnames:
            fpath = os.path.join(root, fname)
            result.append(fpath)
    return result

def list_text_files_current_dir():
    return [x for x in os.listdir('.') if x.endswith('.txt')]

def list_text_files_current_dir():
    import glob
    # will include paths if path provided
    # *.txt                -> no paths
    # ./*.txt              -> everything prefixed with './'
    # /Users/andrewl/*.txt -> everything prefixed with '/Users/andrewl/'
    return glob.glob('*.txt')

def get_files(ext=''):
    return sum([[os.path.join(r, f) for f in
        [f for f in fs if f.endswith(ext)]]
        for (r,d,fs) in os.walk('.')], [])

def replace_in_file():
    fp = open('namegen.py')
    data = fp.read()
    fp.close()

    import re
    
    pattern = re.compile('"[A-Z]+"')
    matches = pattern.findall(data)
    
    for before in matches:
        after = before.lower()
        after = after[0:2].upper() + after[2:]
        #print "%s -> %s" % (before, after)
        data = data.replace(before, after)
    
    print data

def genFileName(ext='', nChars=8):
    random.seed()
    lookup = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ';
    fname = ''
    for i in range(nChars):
        fname += lookup[random.randint(0,len(lookup)-1)]
    return fname + ext


for folder, subfolders, files in os.walk('SomePath'):
  for filename in file:
    if filename.endswith('.srt'):
        os.unlink(os.path.join(folder,filename))

###############################################################################
## calling other processes
###############################################################################

from subprocess import Popen, PIPE
def shellout(cmd):
    print(GREEN + ' '.join(cmd) + NORMAL)
    process = Popen(cmd, stdout=PIPE, stderr=PIPE)
    (stdout, stderr) = process.communicate()
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    print('stdout: -%s-' % stdout)
    print('stderr: -%s-' % stderr)
    process.wait()
    return (stdout, stderr)

shellout(['clang', '-Xclang', '-ast-dump', '-fsyntax-only', fpath])

# if you just want output
output = subprocess.check_output(['ls', '-l']).decode('utf-8')

###############################################################################
## time
###############################################################################

see also [TimeNotes.md](./TimeNotes.md)

def get_iso8601_time():
    seconds = time.time();
    now = time.localtime(seconds)
    return time.strftime("%F", now);
    
def epochToISO8601(epoch: float):
    timeStruct = time.localtime(epoch)
    timeString = time.strftime('%Y-%m-%d', timeStruct)
    return timeString

def ISO8601ToEpoch(isoString: str):
    timeStruct = time.strptime(isoString, '%Y-%m-%d')
    epoch = time.mktime(timeStruct)
    return epoch

# performance timing
import time
t0 = time.perf_counter()
# task
t1 = time.perf_counter()
printf('%f seconds elapsed' % (t1-t0))

###############################################################################
## writing images
###############################################################################

def get_width(fpath):
    image = PIL.Image.open(fpath)
    assert image, 'couldnt open %s' % fpath
    (width, height) = image.size
    return width

def pixel_buf_to_png():
    Image.frombytes('RGB', (100,100), '\xff\x00\x00'*100*100).save('test.png')

def pixel_buf_to_png2():
    # imgdata is a linear list of (r,g,b) tuples
    data = b''.join([struct.pack('BBB', *rgb) for rgb in imgdata])
    Image.frombytes('RGB', (WIDTH,HEIGHT), data).save('feature-map.png')

def set_pixel_array_to_png():
    from PIL import Image
    img = Image.new('RGB', (512,512))
    px = img.load()
    for i in range(512):
        for j in range(512):
            px[i, 511-j] = (0,0,0)
    img.save("/tmp/tmp.png")

def drawing_primitives_to_png():
    from PIL import Image, ImageDraw
    img = Image.new('RGB', (256, 256))
    draw = ImageDraw.Draw(img)
    bgcolor = (0xFF, 0x00, 0x00)
    draw.rectangle([(5,5), (20,20)], fill=bgcolor)
    draw.ellipse((10,10,15,15), fill = 'red', outline ='red') # coords are bounding box
    draw.line((100,100,250,250))
    draw.text((70,70), "hi")
    img.save("/tmp/tmp.png")

def drawsvg(points, path='/tmp/tmp.svg'):
    maxx = max(map(lambda z: z[0], points))
    maxy = max(map(lambda z: z[1], points))
    fp = open(path, 'w')
    fp.write('<?xml version="1.0"?>\n')
    fp.write('<svg width="%f" height="%f" xmlns="http://www.w3.org/2000/svg" version="1.1">\n' % (maxx, maxy))
    fp.write('<path d="M %f %f' % (points[0][0],points[0][1]))
    for c in points[1:]:
        fp.write(' L %f %f' % tuple(c))
    fp.write('" stroke-width="1" stroke-linecap="butt" fill="none" stroke="#000000" />\n')
    fp.write('</svg>\n')
    fp.close()

# draw pixel
img = Image.new('RGB', (256, 256))
# (0, 0) red pixel in top left
img.putpixel((0, 0), (255, 0, 0))
img.save("/tmp/tmp.png")

###############################################################################
## reading images
###############################################################################

def readimg():
    im = Image.open('image.gif')
    #im.width, im.height
    rgb_im = im.convert('RGB')
    r, g, b = rgb_im.getpixel((1, 1))

## plotting graphs
#!/usr/bin/env python
import math
from PIL import Image, ImageDraw
(W,H)=(512,512)
GRID=50
img = Image.new('RGB',(W,H))
px = img.load()
draw = ImageDraw.Draw(img)
for x in xrange(0, W, GRID):
    draw.line((x,0,x,H), fill=(0x40,0x40,0x40))
for y in xrange(0, H, GRID):
    draw.line((0,H-y,W,H-y), fill=(0x40,0x40,0x40))
def plot(pairs, method='points'):
    global px, draw
    last = None
    for (x,y) in pairs:
        y = H-y
        if x<0 or x>=W or y<0 or y>=H:
            last = None
        else:
            if method == 'points':
                px[x,y] = (255,0,0)
            elif method == 'lines' and last:
                draw.line((last[0], last[1], x, y))
            last = (x,y)
points0 = []
points1 = []
for x in range(W):
    points0.append((x, math.sqrt(x)))
    points1.append((x, x**2))
plot(points0, 'points')
plot(points1, 'lines')
img.save("/tmp/tmp.png")

###############################################################################
## ctypes
###############################################################################

import ctypes
gofer = None
cbuf = None
def disasm_libopcodes(arch, mach, insword, addr=0):
    # initialize disassembler, if necessary
    global gofer, cbuf
    if not gofer:
        gofer = ctypes.CDLL("gofer.so")
        cbuf = ctypes.create_string_buffer(256)

    gofer.get_disasm_libopcodes(arch, mach, addr, insword, ctypes.byref(cbuf))
    tmp = cbuf.value.decode('utf-8')
    if tmp[0] == '.':
        return ''
    tmp = re.sub(r' +', ' ', tmp)
    return tmp

###############################################################################
## enumerations
###############################################################################
from enum import Enum, auto, unique

@unique
class Color(Enum):
    RED = 1
    GREEN = 2
    BLUE = 3
    FOO = auto()
    BAR = auto()
    
print(Color.RED)
print(repr(Color.RED))
isinstance(Color.GREEN, Color)
foo = Color.RED
foo.name
foo.value
# check for membership
any(x.value == 5 for x in Fruit)  # True

3 == Color.BLUE # false
3 == Color.BLUE.value # true
Color(3) == Color.BLUE # true

###############################################################################
## graphviz
###############################################################################

def draw_digraph(edges):
    with open('/tmp/tmp.dot', 'w') as fp:
        fp.write('digraph g {\n')
        fp.write('\trankdir=LR;\n')
        for (a,b) in edges:
            fp.write('\t%s -> %s\n' % (a,b))
        fp.write('}\n')
    os.system('dot /tmp/tmp.dot -Tpng -o /tmp/tmp.png')

# pre-declaring vertices and their labels:
print('digraph g {')
print('\t// nodes')
for block in func.low_level_il:
    label = f'bb{block.index} [{block.start},{block.end})'
    print(f'\t{block.index} [label="{label}"]')
print('\t// edges')
for src in func.low_level_il:
    for dst in src.dominator_tree_children:
        print(f'\t{src.index} -> {dst.index}')
print('}')

def graph_nodes(root):
    nodes = root.traverse()

    with open('/tmp/tmp.dot', 'w') as fp:
        fp.write('digraph g {\n')
        fp.write('\t// nodes')
        for n in nodes:
            fp.write(f'\t{id(n)} [label="{n.ttype}"]\n')
        fp.write('\t// edges')
        for a in nodes:
            for b in a.children:
                fp.write(f'\t{id(a)} -> {id(b)}\n')
        fp.write('}')

    os.system('dot /tmp/tmp.dot -Tpng -o /tmp/tmp.png')
    os.system('open /tmp/tmp.png')

def example(root):
    dot = []
    dot.append('digraph G {')

    # global graph settings
    dot.append('// global settings')
    dot.append('node [];')
    dot.append('edge [];')

    # node list
    def all_nodes(n):
        if type(n) == BlockNode:
            return [n]
        else:
            return [n] + sum([all_nodes(c) for c in n.children], [])

    dot.append('// nodes')
    for n in all_nodes(root):
        dot.append(f'{id(n)} [label="{n.__dot__()}"];')

    def all_edges(n):
        if type(n) == BlockNode:
            return []
        result = [(n, c) for c in n.children]
        result = result + sum([all_edges(c) for c in n.children], [])
        return result

    # edge list
    dot.append('// edges')
    for (a, b) in all_edges(root):
        dot.append(f'{id(a)} -> {id(b)}')

    dot.append('}')

    return '\n'.join(dot)

###############################################################################
## hexdump
###############################################################################

def get_hex_dump(data, addr=0, grouping=1, endian='little', color=False):
	result = ''

	while(data):
		ascii = ''
		buff16 = data[0:16]
		data = data[16:]

		if color:
			result += "\x1b[0;33m%08X\x1b[0m " % addr
		else:
			result += "%08X: " % addr

		i = 0
		while i < 16:
			if(i < len(buff16)):
				f0 = { \
					'big':	{1:'>B', 2:'>H', 4:'>I', 8:'>Q'}, \
					'little': {1:'<B', 2:'<H', 4:'<I', 8:'<Q'} \
				}

				f1 = { \
					1:'%02X ', 2:'%04X ', 4:'%08X ', 8:'%016X ' \
				}

				temp = struct.unpack(f0[endian][grouping], buff16[i:i+grouping])[0]

				if color and temp==0:
					result += '\x1b[0;34m' + (f1[grouping] % temp) + '\x1b[0m'
				else:
					result += f1[grouping] % temp

				for j in range(grouping):
					char = buff16[i+j]

					if(char >= ord(' ') and char <= ord('~')):
						ascii += chr(char)
					else:
						if color and char==b'\x00':
							ascii += '\x1b[0;34m.\x1b[0m'
						else:
							ascii += '.'
			else:
				if grouping == 1:
					result += ' '*3
				elif grouping == 2:
					result += ' '*5
				elif grouping == 4:
					result += ' '*9
				elif grouping == 8:
					result += ' '*17

			i += grouping

		result += ' %s\n' % ascii

		addr += 16;

	return result

# shellcode hex dump
# 0x48,0x89,0xE7,                                                  // 0000003C: mov rdi, rsp
# 0x48,0x31,0xC0,                                                  // 00000042: xor rax, rax
# 0x50,                                                            // 00000048: push rax
# 0x57,                                                            // 0000004A: push rdi
# 0x48,0x89,0xE6,                                                  // 0000004C: mov rsi, rsp
from capstone import *
def print_shellcode_buf(code):
    print('uint8_t shellcode[%d] = {' % len(code))
    offset = 0
    md = Cs(CS_ARCH_X86, CS_MODE_64)
    for i in md.disasm(CODE, 0):
        chunk = code[offset:(offset+i.size)]
        left = ''.join(['0x%02X,'%byte for byte in chunk])
        right = '// %08X: %s %s' % (i.address + offset, i.mnemonic, i.op_str)
        print(left.ljust(64), right)
        offset += i.size

# https://gist.github.com/mzpqnxow/a368c6cd9fae97b87ef25f475112c84c
def hexdump(src, addr=0, length=16, sep='.'):
    FILTER = ''.join([(len(repr(chr(x))) == 3) and chr(x) or sep for x in range(256)])
    lines = []
    for c in range(0, len(src), length):
        chars = src[c: c + length]
        hex_ = ' '.join(['{:02x}'.format(x) for x in chars])
        if len(hex_) > 24:
            hex_ = '{}{}'.format(hex_[:24], hex_[24:])
        printable = ''.join(['{}'.format((x <= 127 and FILTER[x]) or sep) for x in chars])
        lines.append('{0:08x}: {1:{2}s} {3:{4}s}'.format(addr+c, hex_, length * 3, printable, length))
    return '\n'.join(lines)

###############################################################################
## misc
###############################################################################

import hashlib
m = hashlib.md5()
m.update(inp)
print ''.join(map(lambda x: '%02X' % ord(x), m.digest()))

import sys
import signal
def signal_handler(sig, foo):
      print('You pressed Ctrl+C')
signal.signal(signal.SIGINT, signal_handler)

for key,value in myDict.items():
  pass

import pickle
a = {'hello': 'world'}
with open('filename.pickle', 'wb') as handle:
    pickle.dump(a, handle, protocol=pickle.HIGHEST_PROTOCOL)
with open('filename.pickle', 'rb') as handle:
    b = pickle.load(handle)
print a == b

# get directory of current script
import pathlib
pathlib.Path(__file__).parent.absolute()
# get current working directory
import pathlib
pathlib.Path().absolute()
# another way (but does not follow symlinks I don't think)
import os, inspect
path = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
# another way, newest:
this_file = inspect.stack()[0][1]
this_dir = os.path.dirname(this_file)
formats_dir = os.path.join(this_dir, '../formats')

# reload module
import importlib
importlib.reload(mymodule)

if 'gvanim' in sys.modules:
    importlib.reload(sys.modules['gvanim'])
    importlib.reload(sys.modules['gvanim.render'])    
from gvanim.render import render_to_svg, hehe
from gvanim import Animation

order = sorted(range(nrows), key=lambda x: self.rows[x], reverse=True)
echelon = BitMatrix(nrows, ncols)
echelon.rows = [self.rows[i] for i in order]
record.rows = [record.rows[i] for i in order]

###############################################################################
## terminal colors
###############################################################################

# method1: manually
(RED, GREEN, YELLOW, NORMAL) = ('\x1B[31m', '\x1B[32m', '\x1B[33m', '\x1B[0m')
print(RED+'red'+NORMAL)
print(YELLOW+'yellow'+NORMAL)
print(GREEN+'green'+NORMAL)
print(f'{RED}Hello, world!{NORMAL}')

# method2: with colorama
from colorama import Fore, Back, Style
print(Fore.GREEN, '; %s has %d basic blocks' % (str(func), len(basic_blocks)), Style.RESET_ALL)
print(f'{Fore.GREEN}; %s has {len(basic_blocks)} basic blocks {Style.RESET_ALL}')

###############################################################################
## json
###############################################################################

# there's a powerful 1:1 correspondence between json and python data structures
import json
# dumps(): dump data structure to string
string = json.dumps(['foo', {'bar': ('baz', None, 1.0, 2)}])
# loads(): load string to data structure
data = json.loads('["foo", {"bar": ["baz", null, 1.0, 2]}]')
# pretty print by adding indent parameter
print(json.dumps(layout, indent=4))

with open('/path/to/config.json') as fp:
    config = json.load(fp)

###############################################################################
## overloading
###############################################################################

# see "3.3.7 Emulating container types" at:
# https://docs.python.org/3/reference/datamodel.html

# Less than                  p1 < p2     p1.__lt__(p2)
# Less than or equal to      p1 <= p2    p1.__le__(p2)
# Equal to                   p1 == p2    p1.__eq__(p2)
# Not equal to               p1 != p2    p1.__ne__(p2)
# Greater than               p1 > p2     p1.__gt__(p2)
# Greater than or equal to   p1 >= p2    p1.__ge__(p2)
# 
# +           object.__add__(self, other)
# -           object.__sub__(self, other)
# *           object.__mul__(self, other)
# @           object.__matmul__(self, other)
# /           object.__truediv__(self, other)
# //          object.__floordiv__(self, other)
# %           object.__mod__(self, other)
# divmod()    object.__divmod__(self, other)
# pow() or ** object.__pow__(self, other[, modulo])
# <<          object.__lshift__(self, other)
# >>          object.__rshift__(self, other)
# &           object.__and__(self, other)
# ^           object.__xor__(self, other)
# |           object.__or__(self, other)

###############################################################################
## *args, *kwargs
###############################################################################
def test0(*foo):
    print('test0:', type(foo), foo)

def test1(**bar):
    print('test1:', type(bar), bar)

test0('A', 'B', 'C')
test1(first='A', second='B', third='C')

# $ ./go.py
# test0: <class 'tuple'> ('A', 'B', 'C')
# test1: <class 'dict'> {'first': 'A', 'second': 'B', 'third': 'C'}

###############################################################################
## OOP, superclass
###############################################################################
class DerivedClass(BaseClass):
    def __init__(self, a, b, c):
        super().__init__(a, b, c)

###############################################################################
## using a temporary file for settings
###############################################################################
import os, re, subprocess, tempfile
(tmp_handle, tmp_name) = tempfile.mkstemp(suffix='.ini')
print("writing temporary contents to %s" % tmp_name)
tmp_obj = os.fdopen(tmp_handle, 'w')
tmp_obj.write('FOO = 23\nBAR = yes\nBAZ = 42123.334\n')
tmp_obj.close()
print("invoking gvim and waiting... (gvim %s)" % tmp_name)
subprocess.call(["vim", '-f', tmp_name])
print("reading changes from %s" % tmp_name)
fp = open(tmp_name)
for line in fp.readlines():
    key, val = re.match(r'([^\s]*?)\s*=\s*(.*)', line.strip()).group(1, 2)
    print(f'{key} = {val}')
fp.close()
