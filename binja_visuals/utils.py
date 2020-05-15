
def function_span(func):
	tmp = [[bb.start, bb.end] for bb in func.basic_blocks]
	tmp = sorted(tmp, key=lambda x:x[0])
	result = []
	curr = tmp[0]
	for foo in tmp[1:]:
		if curr[1] == foo[0]:
			curr[1] = foo[1]
		else:
			result.append(curr)
			curr = foo
	result.append(curr)
	return result
