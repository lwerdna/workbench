#!/usr/bin/python
# find bikes on craigslist, requires BeautifulSoup library

# ~~~ EDIT THIS PART

urls = []
urls.append('orlando.craigslist.org/search/bik')
urls.append('daytona.craigslist.org/search/bik')
urls.append('spacecoast.craigslist.org/search/bik')
urls.append('treasure.craigslist.org/search/bik')

def filter(title, price):
    if price < 200: return True
    if price > 1000: return True
    return False

# ~~~ DONE!

# /search/bik is "by owner"
# /search/bia is "by all"
# /search/bdp is "by dealer"

# test with:
# >>> import find_bikes
# >>> soup = find_bikes.doIt()
# >>> find_bikes = reload(find_bikes)
# etc.

import re
import os
import httplib
from BeautifulSoup import BeautifulSoup

def seenLoad():
    seen = {}
    if os.path.isfile('seen.txt'):
        fp = open('seen.txt', 'r')
        for l in fp.readlines():
            if re.match(r'^\s*$', l):
                continue
            [url, title] = l.split(' ', 1)
            title = title.rstrip()
            seen[url] = title
        fp.close()
    print "loaded %d urls previously seen" % len(seen.keys())
    return seen

def seenSave(seen):
    fp = open('seen.txt', 'w')
    for url in seen.keys():
        if re.match(r'^\s*$', url):
            continue
        fp.write("%s %s\n" % (url, seen[url]))
    fp.close()
    print "saved %d urls previously seen" % len(seen.keys())

def httpGetRequest(base, rest):
    conn = httplib.HTTPConnection(base)
    conn.request("GET", rest)
    resp = conn.getresponse().read()
    conn.close()
    return resp

def doIt():
    global urls

    seen = seenLoad()

    for url in urls:
        idx = url.find('/')
        base = url[0:idx]
        rest = url[idx:]

        print "visiting %s..." % url
        resp = httpGetRequest(base, rest)
        #print resp
    
        soup = BeautifulSoup(resp)

        # looking for "<div class="rows"> ..."
        rows = soup.find('div', {'class':'rows'})
        # looking for all "<p class="row" data-pid="...
        for row in rows:
            # skip any whitespace rows
            # convert BeautifulSoup.NavigableString to string
            if re.match(r'^\s*$', str(row)):
                continue

            # tagParent.tagChild to get child tag
            # tag["href"] to get href attribute
            hdrlink = row.find('a', {'class':'hdrlnk'})
            title = hdrlink.span.text
            sublink = hdrlink['href']
           
            price = 0
            priceElem = row.find('span', {'class':'price'})
            if priceElem:
                price = int(priceElem.text[1:])

            if(filter(title, price)):
                #print "filtered out!"
                continue

            # have we seen it?
            urlFull = base + sublink
            if not urlFull in seen:
                print "%s has \"%s\" for %d" % (urlFull, title, price)
                seen[urlFull] = title
            else:
                #print "seen this before! skipping!"
                pass

    seenSave(seen)

if __name__ == '__main__':
    doIt()
    
