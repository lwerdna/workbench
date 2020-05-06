# space filling curves module

#------------------------------------------------------------------------------
# standard hilbert map and inverse map functions from:
# https://en.wikipedia.org/wiki/Hilbert_curve
#------------------------------------------------------------------------------

def hilbert_rotate_wikipedia(n, x, y, rx, ry):
	if ry == 0:
		if rx == 1:
			x = n-1 - x;
			y = n-1 - y;

		(y,x) = (x,y)

	return (x,y)

def hilbert_d2xy_wikipedia(n, d):
	(x,y,t) = (0,0,d)

	level = 1
	while level<n:
		rx = 1 & (t//2)
		ry = 1 & (t ^ rx)
		(x, y) = hilbert_rotate_wikipedia(level, x, y, rx, ry)
		x += level * rx
		y += level * ry
		t //= 4
		level *= 2

	return (x,y)

def hilbert_xy2d_wikipedia(n, x, y):
	(rx,ry,s,d)=(0,0,0,0)

	s = n//2
	while s > 0:
		rx = int((x & s) > 0)
		ry = int((y & s) > 0)
		d += s * s * ((3 * rx) ^ ry)
		(x, y) = hilbert_rotate_wikipedia(n, x, y, rx, ry)
		s //= 2

	return d

#------------------------------------------------------------------------------
# alternative algorithm
#------------------------------------------------------------------------------

# compute 2d Hilbert curve coordinate from 1d line coordinate
# regions = A B   numerically ordered by entering and leaving line,
#           C D   eg: [A,C,D,B] means enter at A, exit at B, like "U"
def hilbert_d2xy_algo0(length, d, x=0, y=0, regions=list('CABD')):
	#print('d2xy(length=%d, d=%d, (x,y)=(%d,%d), regions=%s' % (length, d, x, y, regions))

	if length == 1:
		return (x,y)

	quarter = length//4

	# compute region index
	if d < quarter: region_idx = 0
	elif d < 2*quarter: region_idx = 1
	elif d < 3*quarter: region_idx = 2
	else: region_idx = 3

	# compute new x,y base
	region = regions[region_idx]
	delta = math.sqrt(length)//2
	if region == 'A':
		y += delta
	elif region == 'D':
		x += delta
	elif region == 'B':
		x += delta
		y += delta

	# compute new region
	if region_idx == 0:
		regions = [regions[i] for i in [0,3,2,1]]
	elif region_idx == 3:
		regions = [regions[i] for i in [2,1,0,3]]

	# recur
	return d2xy(quarter, d-region_idx*quarter, x, y, regions)

#------------------------------------------------------------------------------
# alternative algorithm
#------------------------------------------------------------------------------

def hilbert_d2xy_algo1(length, d, x=0, y=0, kind='H'):
	if length == 1:
		return (x,y)

	# compute quadrant (0 is entering quadrant, 3 is exiting)
	assert not length%4
	quarter = length//4
	marks = [i*quarter for i in [1,2,3,4]]
	quadrant = next(i for i,mark in enumerate(marks) if d<mark)

	# compute new x,y base (coordinate of bottom left corner of subsquare)
	delta = math.sqrt(length)//2
	x_lookup = {'A':[0,1,1,0], 'B':[1,0,0,1], 'C':[1,1,0,0], 'H':[0,0,1,1]}
	y_lookup = {'A':[0,0,1,1], 'B':[1,1,0,0], 'C':[1,0,0,1], 'H':[0,1,1,0]}
	x += x_lookup[kind][quadrant] * delta
	y += y_lookup[kind][quadrant] * delta
	
	kind = {'A':'HAAC', 'B':'CBBH', 'C':'BCCA', 'H':'AHHB'}[kind][quadrant]

	# recur
	return d2xy(length//4, d-quadrant*quarter, x, y, kind)

#------------------------------------------------------------------------------
# region tracing algorithms
#------------------------------------------------------------------------------

def wall_follower(n, d0, d1, mapping, imapping):
	def ok(x, y):
		if x<0 or y<0: return False
		d = imapping(n**2, x, y)
		#print('is %d within %d,%d' % (d, d0, d1))
		return d>=0 and d>=d0 and d<d1

	# move left until stop
	(x,y) = mapping(n**2, d0)
	while 1:
		if x == 0: break
		if not ok(x-1,y): break
		x = x-1

	start = (x,y)
	trace = [start]
	direction = 'down'

	tendencies = ['right', 'down', 'left', 'up']

	while 1:
		#print('at (%d,%d) heading %s' % (x,y,direction))

		tendency = tendencies[(tendencies.index(direction)+1) % 4]

		xmod = {'right':1, 'down':0, 'left':-1, 'up':0}
		ymod = {'right':0, 'down':-1, 'left':0, 'up':1}

		moved = False

		# case A: we can turn right
		x_try = x+xmod[tendency]
		y_try = y+ymod[tendency]
		if ok(x_try, y_try):
			direction = tendency
			(x,y) = (x_try, y_try)
			moved = True
		else:
			# case B: we can continue in current direction
			x_try = x+xmod[direction]
			y_try = y+ymod[direction]
			if ok(x_try, y_try):
				(x,y) = (x_try, y_try)
				moved = True
			else:
				# case C: we can't continue! ah!
				direction = tendencies[(tendencies.index(direction)-1)%4]

		if moved:
			trace.append((x,y))
			
			if (x,y) == start:
				break

	return trace

#------------------------------------------------------------------------------
# misc
#------------------------------------------------------------------------------
