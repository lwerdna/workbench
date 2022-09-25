import re

import z3

def shellout(cmd, input_text=None):
    process = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE)
    if input_text == None:
        (stdout, stderr) = process.communicate()
    else:
        if type(input_text) == str:
            input_text = input_text.encode('utf-8')
        (stdout, stderr) = process.communicate(input=input_text)
    stdout = stdout.decode("utf-8")
    stderr = stderr.decode("utf-8")
    process.wait()
    return (stdout, stderr)

#------------------------------------------------------------------------------
# print conveniences
#------------------------------------------------------------------------------

def pretty_print_z3(expr):
    if expr == None:
        return 'None'

    tmp = z3.simplify(expr)
    if not z3.eq(tmp, expr):
        return pretty_print_z3(tmp)

    clue = expr.decl().name()
    args_ = [expr.arg(i) for i in range(expr.num_args())]
    # bitvector values last
    #breakpoint()

    # try to get named bit vector values on the left
    #args_ = sorted(args_, key=lambda a: 0 if type(a) == z3.z3.BitVecRef else 1)

    substitutions = {'bvadd': '+', 'bvsle':'s<=', 'bvsgt':'s>', 'distinct':'!='}
    clue = substitutions.get(clue, clue)

    result = None
    if False:
        pass
    #elif type(expr) == z3.z3.ArrayRef:
    #    result = '(mem)'
    elif clue == 'concat':
        result = 'concat(' + ', '.join(pretty_print_z3(a) for a in args_) + ')'
    #elif clue == 'extract':
    #    suffix = f'.{expr.size()}'
    #    result = pretty_print_z3(args_[0]) + suffix
    elif clue == 'select':
        # args_[0] is the name of the array
        # args_[1] is the indexing expression
        result = str(args_[0]) + '[' + pretty_print_z3(args_[1]) + ']'
    elif clue == 'store':
        result = 'store(%s, %s, %s)' % \
            (pretty_print_z3(args_[0]), pretty_print_z3(args_[1]), pretty_print_z3(args_[2]))
    elif len(args_) == 2:
        result = pretty_print_z3(args_[0]) + ' ' + clue + ' ' + pretty_print_z3(args_[1])
    #elif clue == '+' or clue == 'bvadd':
    #    result = pretty_print_z3(args_[0]) + '+' + pretty_print_z3(args_[1])
    #elif clue == '=':
    #    result = pretty_print_z3(args_[0]) + '=' + pretty_print_z3(args_[1])
    elif type(expr) == z3.z3.BitVecNumRef:
        result = hex(expr.as_signed_long())
    elif clue == 'bv':
        result = hex(expr.as_signed_long())
    elif clue == 'not':
        result = 'not(' + pretty_print_z3(args_[0]) + ')'
    else:
        result = str(z3.simplify(expr))


    # rsp + -24  ->  rsp - 24
    result = re.sub('\s*\+\s*-\s*', '-', result)

    result = re.sub(r'\s+', ' ', result)

    return result

def pretty_print_z3_array_recursive(expr):
    result = {}

    clue = expr.decl().name()

    if clue == 'store':
        [subarray, addr, value] = expr.children()
        result = pretty_print_z3_array_recursive(subarray)
        result[addr.as_long()] = pretty_print_z3(value)
    else:
        assert False
        #breakpoint()

    return result

def pretty_print_z3_array(expr):
    key_val_mem = pretty_print_z3_array_recursive(expr)

    for addr in sorted(key_val_mem):
        print('0x%08X: %s' % (addr, key_val_mem[addr]))



