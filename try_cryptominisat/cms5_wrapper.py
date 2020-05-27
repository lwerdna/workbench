#!/usr/bin/env python

import os
import re
import tempfile
from subprocess import Popen, PIPE

def call_solver(dimacs):
	process = Popen(['cryptominisat5'], stdout=PIPE, stdin=PIPE)
	(stdout, stderr) = process.communicate(input=dimacs.encode('utf-8'))
	exit_code = process.wait()
	return stdout.decode('utf-8').rstrip()

# input: string like '(A | ~A) & (B | ~B) & (C | ~C)'
# output: ['p cnf 3 3\n1 -1 0\n2 -2 0\n3 -3 0', {'A': 1, 'B': 2, 'C': 3}]
def cnf_to_dimacs(cnf):
	num = 1
	var2idx = {}

	dimacs_lines = []

	for clause in cnf.split(' & '):
		if clause.startswith('(') and clause.endswith(')'):
			clause = clause[1:-1]

		dimacs_line = ''
		for tmp in clause.split(' | '):
			negated = '-' if tmp.startswith('~') else ''
			var_name = tmp[1:] if negated=='-' else tmp

			# lookup or save variable number
			if var_name in var2idx:
				index = var2idx[var_name]
			else:
				index = num
				var2idx[var_name] = num
				num += 1

			# add it to the clause
			dimacs_line += '%s%d ' % (negated, index)

		# terminate clause, add to clauses
		dimacs_lines.append(dimacs_line + '0')

	# produce file
	dimacs = 'p cnf %d %d\n' % (len(var2idx), len(dimacs_lines))
	dimacs += '\n'.join(dimacs_lines)
	return [dimacs, var2idx]

def english_to_cnf(english):
	from sympy import Symbol, And, Or, Not
	from sympy.parsing.sympy_parser import parse_expr
	from sympy.logic.boolalg import to_cnf
	lookup = {'And':And, 'Symbol':Symbol, 'Or':Or, 'Not':Not}
	return str(to_cnf(parse_expr(english, evaluate=False, global_dict=lookup)))

def solve_dimacs(dimacs):
	output = call_solver(dimacs)
	print(output)
	lines = output.split('\n')
	if lines[-2] != 's SATISFIABLE': return False
	if not lines[-1].startswith('v '): return False
	return lines[-1]

def solve_english(english):
	cnf = english_to_cnf(english)
	print(cnf)
	[dimacs, var2idx] = cnf_to_dimacs(cnf)
	print(dimacs)

	idx2var = {}
	for var,num in var2idx.items():
		idx2var[num] = var

	sol_dimacs = solve_dimacs(dimacs)
	# 'v -1 2 -3 0' -> '-1 2 -3'
	if not sol_dimacs: return False
	if not sol_dimacs.startswith('v '): raise Exception('dimacs solution should start with \'v \'')
	if not sol_dimacs.endswith(' 0'): raise Exception('dimacs solution should end with \' 0\'')
	assignments = sol_dimacs[2:-2]

	sol_english = {}
	for assignment in assignments.split(' '):
		if assignment[0]=='-':
			sol_english[idx2var[int(assignment[1:])]] = False
		else:
			sol_english[idx2var[int(assignment)]] = True

	return sol_english

def solve_english_all(english):
	solutions = []

	while True:
		solution = solve_english(english)
		if not solution:
			break

		solutions.append(solution)

		# new clause with inverted variables
		clause = ' | '.join(map(lambda x: '%s%s' %(['','~'][x[1]], x[0]), solution.items()))
		english = english + ' & (%s)' % clause

	return solutions

if __name__ == '__main__':
	# demonstrate https://github.com/sympy/sympy/issues/19439
	tmp = 'Q & S'
	print(english_to_cnf(tmp))

	two_of_three = '(A & B & ~C) | (A & ~B & C) | (~A & B & C)'
	print(english_to_cnf(two_of_three))
	
	print(cnf_to_dimacs('(A | ~A) & (B | ~B) & (C | ~C)'))
