#!/bin/sh

convert -crop 792x612+0+0 /tmp/quick.png /tmp/quick1.png
convert -crop 792x612+792+0 /tmp/quick.png /tmp/quick2.png
convert -crop 792x612+0+612 /tmp/quick.png /tmp/quick3.png
convert -crop 792x612+792+612 /tmp/quick.png /tmp/quick4.png
