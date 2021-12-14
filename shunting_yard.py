#!/usr/bin/env python

# TIL: you can evaluate infix expressions like "3*(4+1)" without the usual parser
#      by converting to postfix with Shunting-yard algorithm, then stack evaluating
#      the resulting postfix/RPN

import os, sys, re, pprint, random

class ParsingException(Exception):
    pass
class MissingLeftParenthesis(ParsingException):
    pass
class MissingRightParenthesis(ParsingException):
    pass

def tokenize(expr):
    expr = re.sub(r'\s+', '', expr)
    return [x for x in re.split(r'(\(|\)|\+|\-|\*|\/|\^|\d+)', expr) if x]

def infix_to_postfix(expr, settings):
    tokens = tokenize(expr)

    def peek(l):
        return l[-1] if l else None

    output = []
    stack = []

    tokens.reverse()
    while tokens:
        token = tokens.pop()

        # token is a number
        if re.match(r'^\d+$', token):
            output.append(token)

        # parentheses
        elif token == '(':
            stack.append(token)
        elif token == ')':
            while True:
                if not stack:
                    raise MissingLeftParenthesis()
                tmp = stack.pop()
                if tmp == '(':
                    break
                output.append(tmp)

        # operators
        else:
            o2 = peek(stack)
            while o2 and \
                  o2 != '(' and \
                  (settings[o2]['precedence'] > settings[token]['precedence'] or \
                  (settings[o2]['precedence'] == settings[token]['precedence'] and settings[token]['associativity'] == 'left')):
                output.append(stack.pop())
                o2 = peek(stack)
            stack.append(token)
            
    while stack:
        if peek(stack) == '(':
            raise MissingRightParenthesis()
        output.append(stack.pop())

    return ' '.join(output)

def evaluate(expr, settings):
    stack = []
    postfix = infix_to_postfix(expr, settings).split(' ')
    for token in postfix:
        if re.match(r'^\d+$', token):
            stack.append(int(token))
            continue

        assert token in settings
        function = settings[token]['function']
        arity = function.__code__.co_argcount

        assert len(stack) >= arity
        args = []
        for i in range(arity):
            args.append(stack.pop())
        args.reverse()

        result = function(*args)
        stack.append(result)

    assert len(stack) == 1
    return stack.pop()

# generate tests:
#
#def gen_random_expr():
#    steps = random.randint(2,10)
#    result = str(random.randint(0,1000))
#    for i in range(steps):
#        result += random.choice(list('+-*/^'))
#        if result[-1] == '^':
#            result += str(random.randint(1,3))
#        else:
#            result += str(random.randint(0,1000))
#        if random.randint(0,1):
#            result = '('+result+')'
#
#    expected = eval(result.replace('^', '**').replace('/', '//'))
#    return 'assert evaluate(\'%s\') == %d' % (result, expected)
#
#for i in range(20):
#    print(gen_random_expr())

if __name__ == '__main__':
    settings = {
        '+': {
            'function': lambda a, b: a+b,
            'precedence': 1,
            'associativity': 'left'
        },
        '-': {
            'function': lambda a, b: a-b,
            'precedence': 1,
            'associativity': 'left'
        },
        '*': {
            'function': lambda a, b: a*b,
            'precedence': 2,
            'associativity': 'left'
        },
        '/': {
            'function': lambda a, b: a//b,
            'precedence': 2,
            'associativity': 'left'
        },
        '^': {
            'function': lambda a, b: a**b,
            'precedence': 3,
            'associativity': 'right'
        }
    }

    # test tokenizer
    assert tokenize('1*(23+456^7890)') == \
        ['1', '*', '(', '23', '+', '456', '^', '7890', ')']
    assert tokenize('3 + 4 * 2 / ( 1 − 5 ) ^ 2 ^ 3   ') == \
        ['3', '+', '4', '*', '2', '/', '(', '1', '−', '5', ')', '^', '2', '^', '3']
    assert tokenize('31 + 42 * 23 / ( 145 − 556 ) ^ 27 ^ 3   ') == \
        ['31', '+', '42', '*', '23', '/', '(', '145', '−', '556', ')', '^', '27', '^', '3']
    assert tokenize('((1+2)*3)') == \
        ['(', '(', '1', '+', '2', ')', '*', '3', ')']

    # text conversion
    assert infix_to_postfix('1*(23+456^7890)', settings) == '1 23 456 7890 ^ + *'
    assert infix_to_postfix('1*23+456^7890', settings) == '1 23 * 456 7890 ^ +'
    assert infix_to_postfix('3 + 4 * 2 / ( 1 - 5 ) ^ 2 ^ 3', settings) == '3 4 2 * 1 5 - 2 3 ^ ^ / +'
    assert infix_to_postfix('3 + 4 * 2 / 1 - 5 ^ 2 ^ 3', settings) == '3 4 2 * 1 / + 5 2 3 ^ ^ -'

    # test evaluation
    assert evaluate('1+1', settings) == 2
    assert evaluate('1+2', settings) == 3
    assert evaluate('1+2*3', settings) == 7
    assert evaluate('(((134^2/31)/687^2+131)*905)^2', settings) == 14055288025
    assert evaluate('((215*396)^1)-342*991', settings) == -253782
    assert evaluate('(((619-39)*552^3)/61)*761', settings) == 1217026537796
    assert evaluate('(((900+392^2)*783)+448)-350', settings) == 121023710
    assert evaluate('(568^2)^1', settings) == 322624
    assert evaluate('((908/659-214)^3+262+466+611)', settings) == -9662258
    assert evaluate('((385+232-704)*486^1)', settings) == -42282
    assert evaluate('(((747-268+414-216)/5)-914+769)', settings) == -10
    assert evaluate('(307/294)*209^3', settings) == 9129329
    assert evaluate('(((((788-660-28)*585)/843)-446)+786)*879', settings) == 359511
    assert evaluate('(((347*108+152+740)-713)^2^1*690*361)-797', settings) == 353184468136453
    assert evaluate('(((484*439)+526+735/248)+163)', settings) == 213167
    assert evaluate('(410/674)/404', settings) == 0
    assert evaluate('((675/942+37)-449)*469', settings) == -193228
    assert evaluate('((((((74^3)+531)*603*903)-926)-976)-68-210)-798', settings) == 220937246317
    assert evaluate('((20^1)-355)', settings) == -335
    assert evaluate('((488*543)-64)', settings) == 264920
    assert evaluate('(((((457-422-400^2^2)+72)-128)/179)^3)+170', settings) == -2925235296229778243775830
    assert evaluate('(((141*598)/127-592)/508*95)/438+363', settings) == 363
    assert evaluate('(((92-762)*196^3)+902)', settings) == -5044788218
    assert evaluate('(((455/533*721*776/582)+379)^3/229)', settings) == 237728
    assert evaluate('((((68/92*261^1/68)*809)/968+589)^1)+254^2', settings) == 65105
    assert evaluate('((707^2*701^3+713)*97)/264', settings) == 63264588695855
    assert evaluate('(((((430*215)+915-566)*392+47^3)+765)+55)', settings) == 36481851
    assert evaluate('((((((580*291)+503)+482-230)^2)^3-823)-458)', settings) == 23744127936964266688387678889344
    assert evaluate('371*302/427', settings) == 262
    assert evaluate('((((975-874+62+200*694)-534)+19/762*394)*826)+742', settings) == 114343096
    assert evaluate('((((5^2*270)/68+306)-740)*461)', settings) == -154435
    assert evaluate('(((895*574)^3^2/546)+765*979)^1^2-16+391', settings) == 4564799499760027453095288864337780584149475108284
    assert evaluate('(632-630)+153/412', settings) == 2
    assert evaluate('((750*315)/787)', settings) == 300
    assert evaluate('(((103/243)^3^3)^2)', settings) == 0
    assert evaluate('960+883*372', settings) == 329436
    assert evaluate('((((((527/30)+466*779)/347)/120)+960*349)-629)', settings) == 334419
    assert evaluate('((955^2^3/640)^1^3)*447*810+552', settings) == 391416870859434792080238252
    assert evaluate('((((375*923)/398)*748/797/367)/528+648)', settings) == 648
    assert evaluate('(429+929^1)', settings) == 1358
    assert evaluate('(((((((729*38)^3)*349-173)*934)*939)+423)/930)', settings) == 6996620556267072138
    assert evaluate('(((((907/292)/789*224)+162)-550/686^2/586)*141)*810', settings) == 18502020
    assert evaluate('((((701-224)+749)*840-59-239^1)+596)', settings) == 1030138

    print('PASS')

