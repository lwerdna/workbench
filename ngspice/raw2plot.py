#!/usr/bin/env python

import re
import os
import sys

varsToPlot = ['v(1)', 'v(2)', 'v(3)', 'v(4)']

fPathIn = 'rawspice.raw'
if sys.argv[1:]:
	fPathIn = sys.argv[1]
fPathOutData = os.path.splitext(fPathIn)[0] + '.dat'
fPathOutPlot = os.path.splitext(fPathIn)[0] + '.plt'
fPathOutPng = os.path.splitext(fPathIn)[0] + '.png'
print 'reading: %s' % fPathIn

title = ''
state = 'header'
numVars = 0
varNames = []
varTypes = []
varValues = []
varValuesI = 0
fp = open(fPathIn, 'r')
for (lineNum,line) in enumerate(fp.readlines()):
	line = line.rstrip()
	#print "[state:%s] processing line: %s" % (state, repr(line))

	if state == 'header':
		m = re.match(r'^Title: (.*)', line)
		if m:
			title = m.group(1)
			continue
		m = re.match(r'^No. Variables: (\d+)', line)
		if m:
			numVars = int(m.group(1))
			varValues = map(lambda x:[], range(numVars))
			continue
		m = re.match(r'No. Points: (\d+)', line)
		if m:
			numPoints = int(m.group(1))
			continue
		if re.match(r'^Variables:', line):
			state = 'variables'
			continue
	elif state == 'variables':
		# eg:	2	v(2)	voltage 
		m = re.match(r'^\s+(\d)+\s+(\S+)\s+(\S+)$', line)
		if m:
			(varIdx,varName,varType) = m.group(1,2,3)
			varIdx = int(varIdx)
			if varIdx != len(varNames):
				raise Exception("line %d: expected variable index %d, got %d" % \
					(lineNum, len(varNames), varIdx))
			varNames.append(varName)
			varTypes.append(varType)
			continue
		# change state out
		if line == 'Values:':
			if len(varNames) != numVars:
				raise Exception('line %d: netlist declared %d variables, but only %d found' % \
					(lineNum, len(varNames), numVars))
			state = 'values'
			continue
		raise Exception('in "variables" state, unexpected: %s' % repr(line))
	elif state == 'values':
		# eg: " 0	0.000000000000000e+00"
		# eg: "	5.000099889684861e-08"
		m1 = re.match(r'^\s*\d+\s+(.*)', line)
		m2 = re.match(r'^\s+(.*)', line)
		if m1 or m2:
			value = None
			if m1:
				if varValuesI != 0:
					raise Exception('line %d: expected to be at var index 0 when encountering new block of values')
				value = m1.group(1)
			else:
				value = m2.group(1)
		
			varValues[varValuesI].append(float(value))
			varValuesI = (varValuesI + 1) % len(varNames);
			continue
		# blank lines separate the value blocks
		if line == '':
			continue
		raise Exception('in "values" state, unexpected: %s' % repr(line))
	else:
		raise Exception('what state am I in?')
fp.close()

#print 'variable names to gnuplot column index:'
#for (i,n) in enumerate(varNames):
#	print '%d: %s' % (i,n) 

# write gnuplot data (.data) file
print 'writing: %s' % fPathOutData
fp = open(fPathOutData, 'w')
fp.write('#' + ' '.join( map(lambda x: '{:14s}'.format(x), varNames) ))
fp.write('\n')
for valIdx in range(len(varValues[0])):
	for varIdx in range(len(varNames)):
		fp.write('{:0.8e} '.format(varValues[varIdx][valIdx]))
	fp.write('\n')
fp.close()

# find min/max time, voltage
minTime = min( varValues[ varNames.index('time') ] )
maxTime = max( varValues[ varNames.index('time') ] )

(mins, maxs) = ([], [])
for varName in varsToPlot:
	mins.append(min(varValues[varNames.index(varName)]))
	maxs.append(max(varValues[varNames.index(varName)]))
minVolt = min(mins)
maxVolt = max(maxs)

# write gnuplot plot (.plt) file
print 'writing: %s' % fPathOutPlot
fp = open(fPathOutPlot, 'w')
fp.write('set terminal png\n')
fp.write('set out \'%s\'\n' % fPathOutPng)
fp.write('set title "%s"\n' % title)
fp.write('set xlabel "time"\n')
fp.write('set ylabel "voltage"\n')
fp.write('set grid\n')
fp.write('unset logscale x\n')
fp.write('set xrange [%0.8e:%0.8e]\n' % (minTime, maxTime))
fp.write('unset logscale y \n')
fp.write('set yrange [%0.8e:%0.8e]\n' % (minVolt-.1*(maxVolt-minVolt), maxVolt+.1*(maxVolt-minVolt)))
fp.write('set format y "%g"\n')
fp.write('set format x "%g"\n')
fp.write('plot ')
plotCmds = []
for name in varsToPlot:
	plotCmds.append('\'%s\' using %d:%d with lines lw 1 title "%s"' % \
		(fPathOutData, varNames.index('time')+1, varNames.index(name)+1, name))
fp.write(','.join(plotCmds) + '\n')
fp.close()
