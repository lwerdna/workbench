# TEST: simple arithmetic expression
# precondition: {'x':[10,20], 'y':[8,9]}
# postcondition: {'x':[20,32], 'y':[8,9]}
x = x + 2*y - 6

# TEST: widest x, constrained by single value (result is x is any value _BUT_ 5)
# precondition: {}
# postcondition: {'x':[6,4]}
if x == 5:
    x = 1234

# TEST: widest x, constrained by a range of values
# precondition: {}
# postcondition: {'x':[0x80000000,0x3e8]}
if x > 1000:
    x = 5

# TEST: determinable if taken (==), x constrained
# precondition: {'x':5}
# postcondition: {'x':0x1234}
if x == 5:
    x = 0x1234

# TEST: determinable if taken (>), x constrained
# precondition: {}
# postcondition: {'x':0x1234}
x = 5
if x > 3:
    x = 0x1234

# TEST: determinable if taken (compound), x constrained
# precondition: {}
# postcondition: {'x':0x1234}
x = 20
if x >= 0 and x <= 1000:
    x = 0x1234

# TEST: on <=, unsigned is more restrictive, signed more permissive, but agnostic must account for both
# precondition: {'y':500}
# postcondition: {'y':[0x80000000,0x3e8], 'x':'anything'}
if x <= 1000:
    y = x

# TEST: on >=, signed is more restrictive, unsigned more permissive, but agnostic must account for both
# precondition: {'y':2000}
# postcondition: {'y':[0x3e8,0xFFFFFFFF], 'x':'anything'}
if x >= 1000:
    y = x

# TEST: determinable if not taken (compound)
# precondition: {}
# postcondition: {'x':20}
x = 20
if x <= 0 and x >= 1000:
    x = 0x1234

# TEST: if statement slices right subset of input variable, maybe enters
# precondition: {'x':[3, 8]}
# postcondition: {'x':[3, 8], 'y':[0,0xFFFFFFFF]}
if x > 5:
    y = x

# TEST: if statement slices left subset of input variable, maybe enters
# precondition: {'x':[3, 8]}
# postcondition: {'x':[3, 8], 'y':[0,0xFFFFFFFF]}
if x < 5:
    y = x

# TEST: if statement slices center subset of input variable, maybe enters
# precondition: {'x':[3, 8]}
# postcondition: {'x':[3, 8], 'y':[0,0xFFFFFFFF]}
if x >= 5 and x <= 6:
    y = x

# TEST: if statement envelopes input variable, ALWAYS enters
# precondition: {'x':[3, 8]}
# postcondition: {'x':[3, 8], 'y':[3, 8]}
if x >= 1 and x <= 10:
    y = x

# TEST: true block taken
# precondition: {}
# postcondition: {'x':1000, 'y':[1,2]}
x = 1000
y = 0
if x >= 5:
    y = 1
else:
    y = 2

# TEST: if and else sometimes execute, but one must, constraining y to 1 or 2
# precondition: {'x':[3, 8]}
# postcondition: {'x':[3, 8], 'y':[1,2]}
y = 0
if x >= 5:
    y = 1
else:
    y = 2

# TEST: if always executes, never else
# precondition: {'x':[3, 8]}
# postcondition: {'x':[3, 8], 'y':1}
y = 0
if x >= 1 and x <= 10:
    y = 1
else:
    y = 2

# TEST: if never executes, else always executes
# precondition: {'x':[3, 8]}
# postcondition: {'x':[3, 8], 'y':2}
y = 0
if x > 9:
    y = 1
else:
    y = 2

# TEST: expression and if statement
# suppose x was unsigned, x is [0, 0x3e9]
# suppose x was signed, x is [0, 0x3e9]
# precondition: {'x':[10,20], 'y':[8,9], 'z':0}
# postcondition: {'x':[20,32], 'y':[8,9], 'z':999}

x = x + 2*y - 6
if x>7:
    z = 999

# TEST: expression and if statement (ignore the else)
# precondition: {'x':[10,20], 'y':[8,9], 'z':0}
# postcondition: {'x':[20,32], 'y':[8,9], 'z':999}
x = x + 2*y - 6
if x>7:
    z = 999
else:
    z = 111

# TEST: expression and if statement (ignore the else)
# precondition: {'x':[10,20], 'y':[8,9], 'z':0}
# postcondition: {'x':[20,32], 'y':[8,9], 'z':111}
x = x + 2*y - 6
if x<7:
    z = 999
else:
    z = 111

# TEST: enhanced boolean analysis
# WITH    ENHANCED BOOLEAN ANALYSIS, post condition is {'x':[0x0,0x3E9]}
# WITHOUT ENHANCED BOOLEAN ANALYSIS, post condition is {'x':[0x80000000,0x3E9]}

# precondition: {}
# postcondition: {'x':[0,0x3E9]}

x = input()
# TRUE/TAKEN
#                            SIGNED                 UNSIGNED         AGNOSTIC (UNION)
#          ------------------------ ------------------------ ------------------------
# x < 0    [0x80000000, 0xFFFFFFFF]                       [] [0x80000000, 0xFFFFFFFF]
# x > 1000 [0x000003E9, 0x7FFFFFFF] [0x000003E9, 0xFFFFFFFF] [0x000003E9, 0x80000000]
# (or)     [0x000003E9, 0xFFFFFFFF] [0x000003E9, 0xFFFFFFFF] [0x000003E9, 0xFFFFFFFF]
#
# and the union of the signed and unsigned views if [0x3E9, 0xFFFFFFFF]
if x < 0 or x > 1000:
    # 0
    x = 0
# FALSE/UNTAKEN
#                             SIGNED                 UNSIGNED         AGNOSTIC (UNION)
#           ------------------------ ------------------------ ------------------------
# x >= 0    [0x00000000, 0x7FFFFFFF] [0x00000000, 0xFFFFFFFF] [0x00000000, 0xFFFFFFFF]
# x <= 1000 [0x80000000, 0x000003E8] [0x00000000, 0x000003E8] [0x80000000, 0x000003E8]
# (and)     [0x00000000, 0x000003E8] [0x000003E8, 0xFFFFFFFF] [0x80000000, 0x000003E8]
else:
    # [0x80000000, 0x000003E8] -> [0x80000001, 0x000003E9]
    x = x + 1

# TEST: simple loop
# precondition: {'x':1}
# postcondition: {'x':[0,0xFFFFFFFF]}
x = 0
while x >= 0:
    x = x + 1

# TEST: simple loop 2
# precondition: {'x':1}
# postcondition: {'x':[0,0xFFFFFFFF]}
x = 1000
while x >= 0:
    x = x + 1

# TEST: enhanced boolean analysis within loop
# precondition: {}
# postcondition: {'i':'anything', 'x':[0,0x3e9]}
i = 1
while i > 0:
    # TRUE/TAKEN
    # x < 0:      [0x80000000, 0xFFFFFFFF]
    # x > 1000:   [0x000003E9, 0x7FFFFFFF]
    # (union)     [0x000003E9, 0xFFFFFFFF]
    if x < 0 or x > 1000:
        x = 0
    # FALSE/UNTAKEN
    # x >= 0:     [0x00000000, 0x7FFFFFFF]
    # x <= 1000:  [0x80000000, 0x000003E8]
    # (union)     [0x00000000, 0x000003E8]
    else:
        x = x + 1

    i = input()

# TEST: special case (x=45 after reaching 50) is within view of 10 iterations
# precondition: {'x':0}
# postcondition: {'x':[45,50]}
x = 45
while x <= 100:
    if x >= 50:
        x = 45
    else:
        x = x + 1

# TEST: special case (x=10 after 50 iterations) is NOT within view of 10 iterations, expect overapproximation
# precondition: {'x':[10,20]}
# postcondition: {'x':[1,0x7FFFFFFF]}
x = 0
while x <= 100:
    if x >= 50:
        x = 10
    else:
        x = x + 1

