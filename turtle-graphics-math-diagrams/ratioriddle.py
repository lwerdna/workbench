#!/usr/bin/env python3

import math
from turtle import *

def stateSave():
    return {
        'pen': pen(),
        'position': position(),
        'heading': heading()
    }

def stateRestore(state):
    penup()
    setposition(state['position'])
    setheading(state['heading'])
    pen(state['pen'])

def hop(x=0, y=0):
    penState = pen()
    penup()
    setposition(x, y)
    pen(penState)

def square(length):
    for k in range(4):
        forward(length)
        right(90)

def grid(length, c='#B0B0B0'):
    width = window_width()
    height = window_height()
    #print("width (w,h)=(%d,%d)" % (width, height))

    nGridsX = (width/2 + length - 1)/length
    nGridsY = (height/2 + length - 1)/length
    #print("grids in a quadrant = (%d,%d)" % (nGridsX, nGridsY))

    s = stateSave()
    color(c)
    setheading(90)

    x = -1 * nGridsX
    while x < nGridsX:
        y = -1*nGridsY
        while y < nGridsY:
            hop(x*length, y*length)
            square(length)
            y += 1
        x += 1
    stateRestore(s)

def background(c='#C0FFE0'):
    width = window_width()
    height = window_height()

    # this alone isn't sufficient: postscript output doesn't contain it
    #bgcolor(c)
    s = stateSave()
    (xcoord, ycoord) = (-1*((width+1)/2), (height+1)/2)
    print("drawing background rect at (%d,%d)" % (xcoord, ycoord))
    hop(-1*((width+1)/2), (height+1)/2)
    setheading(0)
    color(c, c)
    pendown()
    begin_fill()
    forward(width)
    right(90)    
    forward(height)
    right(90)    
    forward(width)
    right(90)    
    forward(height)
    right(90)
    end_fill()
    stateRestore(s)

def title(text, color_="black", font_=("Arial", 16, "normal")):
    width = window_width()
    height = window_height()
    textPosX = -1 * (width/2) + 8
    textPosY = height/2 - 24

    s = stateSave()
    color(color_)
    hop(textPosX, textPosY)
    write(text, align="left", font=font_)
    stateRestore(s)

def saveImage(fname):
    cv = getcanvas()
    cv.update()
    cv.postscript(file="temp.ps", colormode='color')

if __name__ == '__main__':
    # no delay
    tracer(0, 0)

    L = 90

    # <class 'turtle._Screen'>
    screen = Screen()

    print("available shapes: " % screen.getshapes())
    screen.setup(480, 360)

    width = screen.window_width()
    height = screen.window_height()
    print("window (w,h)=(%d,%d)" % (width, height))
    width = window_width()
    height = window_height()
    print("window (w,h)=(%d,%d)" % (width, height))

    background()
    grid(L)

    # circle
    color("blue")
    setheading(90)
    hop(math.sqrt(2)*L, 0)
    circle(math.sqrt(2)*L, None, 256)

    #tracer(1,1)
    pensize(2)
    hop()
    color("black")
    setheading(90)
    square(L)
    setheading(180)
    square(L)
    setheading(45)
    color("red")
    square(math.sqrt(2)*L)

    title("brilliant.org 100 Day Summer Challenge: 81 of 100: Ratio Riddle");
    hideturtle()
    update()

    saveImage("foo.png")

    exitonclick()

