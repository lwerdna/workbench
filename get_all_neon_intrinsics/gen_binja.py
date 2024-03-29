#!/usr/bin/env python

import re
import sys

from collections import OrderedDict

def ntype_to_binja_types(ntype):
	# remove pointer
	if ntype.endswith(' const *'):
		ntype = ntype[0:-8]
	if ntype.endswith(' *'):
		ntype = ntype[0:-2]

	binja_type = 'Float' if 'float' in ntype else 'Int'

	# int (for lane or immediate)
	if ntype == 'int':
		return ['Type::IntegerType(4)']

	# multiple packed, eg: "uint8x8x2_t"
	m = re.match(r'^(\w+?)(\d+)x(\d+)x(\d+)_t$', ntype)
	if m:
		(base, bit_width, npacked, nregs) = m.group(1,2,3, 4)
		return ['Type::%sType(%d)' % (binja_type, int(bit_width)*int(npacked)/8)]*int(nregs)

	# packed in registers, eg: "int8x8_t"
	m = re.match(r'^(\w+?)(\d+)x(\d+)_t$', ntype)
	if m:
		(base, bit_width, npacked) = m.group(1,2,3)
		return ['Type::%sType(%d)' % (binja_type, int(bit_width)*int(npacked)/8)]

	# simple, eg: "int8_t"
	m = re.match(r'^(\w+?)(\d+)_t$', ntype)
	if m:
		(base, bit_width) = m.group(1,2)
		return ['Type::%sType(%d)' % (binja_type, int(bit_width)/8)]

	raise Exception('cannot convert neon type %s into binja type' % ntype)


class LineSipper:
	def __init__(self, fp):
		self.i = 0
		self.lines = [x.rstrip() for x in fp.read().splitlines()]

	def sip(self, predicate):
		result = []
		while not self.empty():
			line = self.lines[self.i]
			if not predicate(line): break
			result.append(line)
			self.i += 1
		return result

	def peek(self):
		if self.i >= len(self.lines): return ''
		return self.lines[self.i]

	def unconsume(self):
		self.i -= 1

	def consume(self):
		assert not self.empty()
		tmp = self.peek()
		self.i += 1
		print('consumed %s' % repr(tmp))
		return tmp

	def empty(self):
		return self.i >= len(self.lines)

class Intrinsic():
	def from_lines(self, sipper):
		# parse FSIG
		assert sipper.peek().startswith('FSIG: ')
		self.fsig = sipper.consume()[6:]
		m = re.match(r'^(\w+) (\w+)\((.*)\)', self.fsig)
		(self.ret_type, self.name, args) = m.group(1,2,3)
		self.arg_names = []
		self.arg_types = []
		for type_name in args.split(', '):
			type_name = type_name.replace('const ', '')
			(type_, name) = type_name.rsplit(' ', 1)

			# split stuff like int16x4x2_t into into int16x4, int16x4
			#m = re.match(r'^(\w+?\d+x\d+)x(\d+)_t$', type_)
			self.arg_types.append(type_)
			self.arg_names.append(name)

		# parse ASIG
		self.asig = re.match(r'^ASIG: ?(.*)$', sipper.consume()).group(1)
		# parse ARGPREP
		while not sipper.consume().startswith('ARGPREP:'):
			pass
		self.argprep = OrderedDict()
		while sipper.peek().startswith('\t'):
			if 'lane' in sipper.peek():
				varname = re.search(r'lane\d*', sipper.peek()).group(0)
				self.argprep[varname] = varname
			elif ' n ' in sipper.peek():
				self.argprep['n'] = '<n>'
			elif ' imm' in sipper.peek():
				varname = re.search(r'imm\d*', sipper.peek()).group(0)
				self.argprep[varname] = varname
			else:
				m = re.match(r'\t(.*) -> (.*)$', sipper.peek())
				self.argprep[m.group(1)] = m.group(2)
			sipper.consume()

		# parse RESULTS
		assert sipper.consume().startswith('RESULTS:')
		self.results = OrderedDict()
		while sipper.peek().startswith('\t'):
			m = re.match(r'\t(.*) -> (.*)$', sipper.peek())
			self.results[m.group(1)] = m.group(2)
			sipper.consume()

		# skip to end
		while sipper.peek() != '':
			sipper.consume()

	def binja_input_types(self):
		print(str(self))
		assert len(self.arg_types) == len(self.argprep)

	def binja_output_types(self):
		n_results = 0
		for (name, operand) in self.results.items():
			if name in ['ptr', 'void']:
				continue
			n_results += 1

		result = [] if self.ret_type=='void' else ntype_to_binja_types(self.ret_type)
		assert len(result) == n_results
		return ', '.join(result)

	def __str__(self):
		result = 'FSIG: %s %s(' % (self.ret_type, self.name)
		for i in range(len(self.arg_names)):
			result += '%s %s' % (self.arg_types[i], self.arg_names[i])
			if i != len(self.arg_names)-1:
				result += ', '
		result += ')\n'
		result += 'ASIG: %s\n' % self.asig
		result += 'ARGPREP:\n'
		for (k,v) in self.argprep.items():
			result += '\t%s -> %s\n' % (k,v)
		result += 'RESULTS:\n'
		for (k,v) in self.results.items():
			result += '\t%s -> %s\n' % (k,v)
		#result += '\n'
		#result += '\tBINJA_OUTPUT: ' + self.binja_output_types()
		return result

if __name__ == '__main__':
	sipper = None
	with open('intrinsics.txt') as fp:
		sipper = LineSipper(fp)

	intrinsics = []
	while not sipper.empty():
		print('startswith: -%s-' % sipper.peek())
		assert sipper.peek().startswith('FSIG:')
		intrinsic = Intrinsic()
		intrinsic.from_lines(sipper)
		assert sipper.peek() == ''
		sipper.consume()

		if 'vreinterpret' in intrinsic.name: continue
		if intrinsic.asig.startswith('RESULT[I]'): continue
		if len(intrinsic.results)==1 and 'void' in intrinsic.results: continue
		if re.match(r'^st\d+', intrinsic.name): continue
		if re.match(r'^vst\d+', intrinsic.name): continue
		if re.match(r'^ld\d+', intrinsic.name): continue
		if re.match(r'^vld\d+', intrinsic.name): continue
		if re.match(r'^vtbl\d+', intrinsic.name): continue
		if re.match(r'^vtbx', intrinsic.name): continue
		if re.match(r'^vqtbl', intrinsic.name): continue
		if re.match(r'^vqtbx', intrinsic.name): continue
		intrinsics.append(intrinsic)

	cmd = sys.argv[1]
	if cmd in ['dump']:
		for intrinsic in intrinsics:
			print(intrinsic)
	elif cmd in ['output', 'outputs', 'getintrinsicoutputs']:
		type_to_intrinsics = {}
		for intrinsic in intrinsics:
			type_ = intrinsic.binja_output_types()
			if not type_ in type_to_intrinsics:
				type_to_intrinsics[type_] = []
			type_to_intrinsics[type_].append(intrinsic.name)
		for type_ in sorted(type_to_intrinsics):
			for name in sorted(type_to_intrinsics[type_]):
				print('\t\tcase ARM_INTRINS_%s:' % name.upper())
			print('\t\t\treturn {%s};' % type_)
	elif cmd in ['input', 'inputs', 'getintrinsicinputs']:
		type_to_intrinsics = {}
		for intrinsic in intrinsics:
			intrinsic.binja_input_types()

#			type_ = intrinsic.binja_output_types()
#			if not type_ in type_to_intrinsics:
#				type_to_intrinsics[type_] = []
#			type_to_intrinsics[type_].append(intrinsic.name)
#		for type_ in sorted(type_to_intrinsics):
#			for name in sorted(type_to_intrinsics[type_]):
#				print('\t\tcase ARM_INTRINS_%s:' % name.upper())
#			print('\t\t\treturn {%s};' % type_)

