#!/usr/bin/env python

import os, sys, re, pprint
import math

import colorsys

from PIL import Image # pip install pillow

# x,y coordinates (Cartesian) to hue, saturation
def xy_to_hs(x, y):
    # translate to center (128, 128)
    (delta_x, delta_y) = (x-128, y-128)

    #if abs(delta_x) < .0001:
    #    return (0, 0) # 0 degrees hue, 0 saturation

    #angle_rad = math.atan(delta_y / delta_x)
    angle_rad = math.atan2(delta_y, delta_x)
    if angle_rad < 0:
        angle_rad += 2 * math.pi
    angle_01 = angle_rad / (2 * math.pi) # angle as [0,1]

    #breakpoint()
    
    dist = math.sqrt(delta_x**2 + delta_y**2)
    dist_01 = dist / 181.0193 # distances as [0,1]

    return (angle_01, dist_01)

def cartesian_to_pil(x, y):
    return (x, 255-y)

if __name__ == '__main__':
    # (0, 0) is in top left
    img = Image.new('RGB', (256, 256))

    # loop over Cartesian (x, y)
    for x in range(0, 256):
        for y in range(0, 256):
            # leave black on checkered squares
            if not (x & 0x20) ^ (y & 0x20):
                continue

            v = 1.0
            (h, s) = xy_to_hs(x, y)
            (r, g, b) = colorsys.hsv_to_rgb(h, s, v)

            # [0.0,1.0] -> [0,256)
            [r, g, b] = [int(255*c) for c in [r, g, b]]

            (x, y) = cartesian_to_pil(x, y)

            img.putpixel((x, y), (r, g, b))

    img.save("/tmp/tmp.png")
