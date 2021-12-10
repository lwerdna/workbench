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

def infix_to_postfix(expr):
    tokens = tokenize(expr)

    precedence = {'+':1, '-':1, '*':2, '/':2, '^':3}
    associativity = {'+':'left', '-':'left', '*':'left', '/':'left', '^':'right'}

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
                  (precedence[o2] > precedence[token] or \
                  (precedence[o2] == precedence[token] and associativity[token] == 'left')):
                output.append(stack.pop())
                o2 = peek(stack)
            stack.append(token)
            
    while stack:
        if peek(stack) == '(':
            raise MissingRightParenthesis()
        output.append(stack.pop())

    return ' '.join(output)

def evaluate(expr):
    stack = []
    for token in infix_to_postfix(expr).split(' '):
        if re.match(r'^\d+$', token):
            stack.append(int(token))
            continue

        assert len(stack) >= 2
        b = stack.pop()
        a = stack.pop()

        if token == '+': c = a + b
        elif token == '-': c = a - b
        elif token == '*': c = a * b
        elif token == '/': c = a // b # integer division to avoid float and rounding complications
        elif token == '^': c = a ** b

        stack.append(c)

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
    assert infix_to_postfix('1*(23+456^7890)') == '1 23 456 7890 ^ + *'
    assert infix_to_postfix('1*23+456^7890') == '1 23 * 456 7890 ^ +'
    assert infix_to_postfix('3 + 4 * 2 / ( 1 - 5 ) ^ 2 ^ 3') == '3 4 2 * 1 5 - 2 3 ^ ^ / +'
    assert infix_to_postfix('3 + 4 * 2 / 1 - 5 ^ 2 ^ 3') == '3 4 2 * 1 / + 5 2 3 ^ ^ -'

    # test evaluation
    assert evaluate('1+1') == 2
    assert evaluate('1+2') == 3
    assert evaluate('1+2*3') == 7
    assert evaluate('(((134^2/31)/687^2+131)*905)^2') == 14055288025
    assert evaluate('((215*396)^1)-342*991') == -253782
    assert evaluate('(((619-39)*552^3)/61)*761') == 1217026537796
    assert evaluate('(((900+392^2)*783)+448)-350') == 121023710
    assert evaluate('(568^2)^1') == 322624
    assert evaluate('((908/659-214)^3+262+466+611)') == -9662258
    assert evaluate('((385+232-704)*486^1)') == -42282
    assert evaluate('(((747-268+414-216)/5)-914+769)') == -10
    assert evaluate('(307/294)*209^3') == 9129329
    assert evaluate('(((((788-660-28)*585)/843)-446)+786)*879') == 359511
    assert evaluate('(((347*108+152+740)-713)^2^1*690*361)-797') == 353184468136453
    assert evaluate('(((484*439)+526+735/248)+163)') == 213167
    assert evaluate('(410/674)/404') == 0
    assert evaluate('((675/942+37)-449)*469') == -193228
    assert evaluate('((((((74^3)+531)*603*903)-926)-976)-68-210)-798') == 220937246317
    assert evaluate('((20^1)-355)') == -335
    assert evaluate('((488*543)-64)') == 264920
    assert evaluate('(((((457-422-400^2^2)+72)-128)/179)^3)+170') == -2925235296229778243775830
    assert evaluate('(((141*598)/127-592)/508*95)/438+363') == 363
    assert evaluate('(((92-762)*196^3)+902)') == -5044788218
    assert evaluate('(((455/533*721*776/582)+379)^3/229)') == 237728
    assert evaluate('((((68/92*261^1/68)*809)/968+589)^1)+254^2') == 65105
    assert evaluate('((707^2*701^3+713)*97)/264') == 63264588695855
    assert evaluate('(((((430*215)+915-566)*392+47^3)+765)+55)') == 36481851
    assert evaluate('((((((580*291)+503)+482-230)^2)^3-823)-458)') == 23744127936964266688387678889344
    assert evaluate('371*302/427') == 262
    assert evaluate('((((975-874+62+200*694)-534)+19/762*394)*826)+742') == 114343096
    assert evaluate('((((5^2*270)/68+306)-740)*461)') == -154435
    assert evaluate('(((895*574)^3^2/546)+765*979)^1^2-16+391') == 4564799499760027453095288864337780584149475108284
    assert evaluate('(632-630)+153/412') == 2
    assert evaluate('((750*315)/787)') == 300
    assert evaluate('(((103/243)^3^3)^2)') == 0
    assert evaluate('960+883*372') == 329436
    assert evaluate('((((((527/30)+466*779)/347)/120)+960*349)-629)') == 334419
    assert evaluate('((955^2^3/640)^1^3)*447*810+552') == 391416870859434792080238252
    assert evaluate('((((375*923)/398)*748/797/367)/528+648)') == 648
    assert evaluate('(429+929^1)') == 1358
    assert evaluate('(((((((729*38)^3)*349-173)*934)*939)+423)/930)') == 6996620556267072138
    assert evaluate('(((((907/292)/789*224)+162)-550/686^2/586)*141)*810') == 18502020
    assert evaluate('((((701-224)+749)*840-59-239^1)+596)') == 1030138

    print('PASS')

