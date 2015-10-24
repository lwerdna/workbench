#!/usr/bin/python
# delete all posts by a single user (to remove spam, etc.)

USER = 'jahan'
COOKIE = 'Cookie: PHPSESSID=jddcsqkvi4vidh5o2340q26c83; _ga=GA1.2.1908081374.1445613284; _gat=1'

#
# tools:
# $ sudo tcpdump -s0 -X -i eth0 'tcp port 80 and host crackmes.de'
# $ sudo tcpdump -s0 -A -i eth0 'tcp port 80 and host crackmes.de'
# snaplen infinity, hex/ascii dump, eth0 interface

# /users/<user>/<crackme>/browse (shows files)
# /users/<user>/<crackme>/download (shows files)
# /users/<user>/<crackme>/vote/X (vote X (1,2,3,4,5))
# /users/<user>/<crackme>/solutions/<solver> (show solution)
# /users/<user>/<crackme>/open (reopen solutions)

import re
import sys
import socket
import threading
from BeautifulSoup import BeautifulSoup

def httpGetRequest(subUrl):
    global COOKIE
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.connect(('www.crackmes.de', 80))
    req = 'GET %s HTTP/1.1\x0d\x0aHost: www.crackmes.de\x0d\x0aUser-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:35.0) Gecko/20100101 Firefox/35.0\x0d\x0aAccept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\x0d\x0aAccept-Language: en-US,en;q=0.5\x0d\x0aAccept-Encoding: gzip, deflate\x0d\x0aReferer: http://www.crackmes.de/users/greedy_fly/crackme_v1.2/\x0d\x0a'
    req += COOKIE 
    req += '\x0d\x0a'
    req += 'Connection: keep-alive\x0d\x0a\x0d\x0a'
    req = req % subUrl
    sock.send(req)

    # get all response, close
    resp = ''
    while 1:
        temp = sock.recv(4096)
        if not temp: break
        resp += temp
    sock.close()

    # done
    return resp

class delThread(threading.Thread):
    def __init__(self, subUrl):
        threading.Thread.__init__(self)
        self.subUrl = subUrl
        print "delThread(%s) created" % subUrl

    def run(self):
        httpGetRequest(self.subUrl)
        print 'delThread(%s) finished' % self.subUrl

# use list_all_crackmes.py to produce this file
with open('allcrackmes.txt') as f:
    urls = f.readlines()

for (urlIdx, url) in enumerate(urls):

    if re.match(r'^#', url): continue
    url = url.strip()
    m = re.match(r'^http://www.crackmes.de(.*)', url)
    subUrl = m.group(1)

    print "on url %d/%d %s, seeking %s" % (urlIdx, len(urls), url, subUrl)
    resp = httpGetRequest(subUrl)

    delUrls = []
    soup = BeautifulSoup(resp)
    foo = soup.find('table', { 'class':"talk" })

    # no comments?
    if not foo:
        continue

    comRows = foo.contents
    for com in comRows:
        # get author
        # eg: '<a title="View profile for acruel" href="/users/acruel">\nacruel\n</a>'
        author = com.a['title'][17:]
        # get delete link
        removeLink = com.td.a["href"]
            
        print "delete author \"%s\" with link %s?" % (author, removeLink),
       
        if author == USER:
            print "YES"
            delUrls.append(removeLink)
        else:
            print "NO"

    # thread and delete 'em
    threads = []
    print "creating delete threads..."
    for subUrl in delUrls:
        threads.append(delThread(subUrl));
    print "activating delete threads..."
    for thread in threads:
        thread.start()
    print "waiting for threads to finish..."
    while threading.activeCount() > 1:
        pass
    

