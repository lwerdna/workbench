# originall from https://nbviewer.org/gist/rpmuller/5666810

import xml.etree.ElementTree as ET

from IPython.display import SVG

class SVGScene:
    def __init__(self):
        self.items = []
        self.height = 400 # override with bbox calculation
        self.width = 400 # override with bbox calculation
        return

    def add(self,item):
        self.items.append(item)
        
    def bbox(self,border=0,BIG=1e10):
        self.xmin = self.ymin = BIG
        self.xmax = self.ymax = -BIG
        for item in self.items:
            xmin,xmax,ymin,ymax = item.bbox()
            self.xmin = min(self.xmin,xmin)
            self.xmax = max(self.xmax,xmax)
            self.ymin = min(self.ymin,ymin)
            self.ymax = max(self.ymax,ymax)
        self.xmin -= border
        self.ymin -= border
        self.xmax += border
        self.ymax += border
        self.height = self.ymax
        self.width = self.xmax
        return
    
    def _repr_svg_(self):
        return self.to_svg()
    
    def to_svg(self):
        self.bbox(10)
        svg = ET.Element('svg', xmlns="http://www.w3.org/2000/svg", version="1.1",
                        height="%s" % self.height, width="%s" % self.width)
        g = ET.SubElement(svg,"g",style="fill-opacity:1.0; stroke:black; stroke-width:1;")
        for item in self.items:
            item.to_svg(g)
        #ET.dump(svg) # useful for debugging
        blob = ET.tostring(svg)
        if type(blob) == bytes:
            blob = blob.decode('utf-8')
        return blob

    def line(self,start,end):
        self.items.append(Line(start,end))

    def circle(self,center,radius,color='blue'):
        self.items.append(Circle(center,radius,color))

    def rectangle(self,origin,height,width,color='blue'):
        self.items.append(Rectangle(origin,height,width,color))

    def text(self,origin,text,size=24):
        self.items.append(Text(origin,text,size))
    
class Line:
    def __init__(self,start,end):
        self.start = start #xy tuple
        self.end = end     #xy tuple
        return
    
    def to_svg(self,parent):
        ET.SubElement(parent,"line",x1=str(self.start[0]),y1=str(self.start[1]),x2=str(self.end[0]),y2=str(self.end[1]))

    def bbox(self):
        return min(self.start[0],self.end[0]),max(self.start[0],self.end[0]),min(self.start[1],self.end[1]),max(self.start[1],self.end[1])

class Circle:
    def __init__(self,center,radius,color):
        self.center = center #xy tuple
        self.radius = radius #xy tuple
        self.color = color   #rgb tuple in range(0,256)
        return
    
    def to_svg(self,parent):
        color = colorstr(self.color)
        ET.SubElement(parent,"circle",cx=str(self.center[0]),cy=str(self.center[1]),r=str(self.radius),
                      style="fill:%s;" % color)

    def bbox(self):
        return self.center[0]-self.radius,self.center[0]+self.radius,self.center[1]-self.radius,self.center[1]+self.radius

class Rectangle:
    def __init__(self,origin,height,width,color):
        self.origin = origin
        self.height = height
        self.width = width
        self.color = color
        return

    def to_svg(self,parent):
        color = colorstr(self.color)
        ET.SubElement(parent,"rect",x=str(self.origin[0]),y=str(self.origin[1]),height=str(self.height),
                      width=str(self.width),style="fill:%s;" % color)

    def bbox(self):
        return self.origin[0],self.origin[0]+self.width,self.origin[1],self.origin[1]+self.height

class Text:
    def __init__(self,origin,text,size=24):
        self.origin = origin
        self.text = text
        self.size = size
        return

    def to_svg(self,parent):
        fs = "font-size"
        el = ET.SubElement(parent,"text",x=str(self.origin[0]),y=str(self.origin[1]))
        el.set("font-size",str(self.size))
        el.text = self.text
    
    def bbox(self):
        return self.origin[0],self.origin[0]+self.size,self.origin[1],self.origin[1]+self.size # Guessing here
    
def colorstr(rgb): 
    if type(rgb) == type(""): return rgb
    return "#%x%x%x" % (int(rgb[0]/16), int(rgb[1]/16), int(rgb[2]/16))
