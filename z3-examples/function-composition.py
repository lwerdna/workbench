#!/usr/bin/env python

import z3

English = z3.Datatype('English')
English.declare('One')
English.declare('Two')
English.declare('Three')
English.declare('Four')
English.declare('Five')
English.declare('Six')
English.declare('Seven')
English.declare('Eight')
English.declare('Nine')
English.declare('Ten')
English = English.create()

Spanish = z3.Datatype('Spanish')
Spanish.declare('Uno')
Spanish.declare('Dos')
Spanish.declare('Tres')
Spanish.declare('Cuatro')
Spanish.declare('Cinco')
Spanish.declare('Seis')
Spanish.declare('Siete')
Spanish.declare('Ocho')
Spanish.declare('Nueve')
Spanish.declare('Diez')
Spanish.declare('Nada')
Spanish = Spanish.create()

def f(x):
    return z3.If(x == English.One, 1,
        z3.If(x == English.Two, 2,
        z3.If(x == English.Three, 3,
        z3.If(x == English.Four, 4,
        z3.If(x == English.Five, 5,
        z3.If(x == English.Six, 6,
        z3.If(x == English.Seven, 7,
        z3.If(x == English.Eight, 8,
        z3.If(x == English.Nine, 9,
        z3.If(x == English.Ten, 10, -1))))))))))

def g(x):
    return z3.If(x == 1, 1,
        z3.If(x == 2, 4,
        z3.If(x == 3, 9,
        z3.If(x == 4, 16,
        z3.If(x == 5, 25,
        z3.If(x == 6, 36,
        z3.If(x == 7, 49,
        z3.If(x == 8, 64,
        z3.If(x == 9, 81,
        z3.If(x == 10, 100, -1))))))))))

def h(x):
    return z3.If(x == 1, Spanish.Uno,
        z3.If(x == 2, Spanish.Dos,
        z3.If(x == 3, Spanish.Tres,
        z3.If(x == 4, Spanish.Cuatro,
        z3.If(x == 5, Spanish.Cinco,
        z3.If(x == 6, Spanish.Seis,
        z3.If(x == 7, Spanish.Siete,
        z3.If(x == 8, Spanish.Ocho,
        z3.If(x == 9, Spanish.Nueve,
        z3.If(x == 10, Spanish.Diez, Spanish.Nada))))))))))

s = z3.Solver()
x = z3.Const('x', English)
s.add(h(g(f(x))) == Spanish.Nueve)
assert s.check() == z3.sat
m = s.model()
print(m[x])

