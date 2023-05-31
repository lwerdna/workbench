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

