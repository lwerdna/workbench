#!/usr/bin/python
# delete all posts by a single user (to remove spam, etc.)
#
# tools:
# $ sudo tcpdump -s0 -X -i eth0 'tcp port 80 and host crackmes.de'
# $ sudo tcpdump -s0 -A -i eth0 'tcp port 80 and host crackmes.de'
# snaplen infinity, hex/ascii dump, eth0 interface

#
# so it seeks /users/kkr_we_rule/asm_keygen_me_1/remove/50249 
#
# aside: each crackme page has:
# /users/<user>/<crackme>/browse (shows files)
# /users/<user>/<crackme>/download (shows files)
# /users/<user>/<crackme>/vote/X (vote X (1,2,3,4,5))
# /users/<user>/<crackme>/solutions/<solver> (show solution)
#
# /users/<user>/<crackme>/open (reopen solutions)
#
# well how do we find these links?
# I found no better way than just go thru EVERY crackme :(

import re
import socket
from BeautifulSoup import BeautifulSoup

# use list_all_crackmes.py to produce this file
with open('allcrackmes.txt') as f:
    urls = f.readlines()

for url in urls:
    # skip comments
    if re.match(r'^#', url): continue

    #
    url = url.strip()
    m = re.match(r'^http://www.crackmes.de(.*)', url)
    tail = m.group(1)
    print "on url: %s, seeking %s" % (url, tail)
    print '--------------------------------------------------------------'
    
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.connect(('www.crackmes.de', 80))
    req = 'GET %s HTTP/1.1\x0d\x0aHost: www.crackmes.de\x0d\x0aUser-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:35.0) Gecko/20100101 Firefox/35.0\x0d\x0aAccept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\x0d\x0aAccept-Language: en-US,en;q=0.5\x0d\x0aAccept-Encoding: gzip, deflate\x0d\x0aReferer: http://www.crackmes.de/users/greedy_fly/crackme_v1.2/\x0d\x0aCookie: PHPSESSID=jddcsqkvi4vidh5o2340q26c83; _ga=GA1.2.1908081374.1445613284; _gat=1\x0d\x0aConnection: keep-alive\x0d\x0a\x0d\x0a' % tail
    sock.send(req)

    # get all response, close
    resp = ''
    while 1:
        temp = sock.recv(4096)
        if not temp: break
        resp += temp
    sock.close()

    soup = BeautifulSoup(resp)
    foo = soup.find('table', { 'class':"talk" })
    comRows = foo.contents
    for com in comRows:
        # get author
        # eg: '<a title="View profile for acruel" href="/users/acruel">\nacruel\n</a>'
        author = com.a['title'][17:]
        # get delete link
        removeLink = com.td.a["href"]
        
        print "delete author -%s- with link -%s-" % (author, removeLink)


