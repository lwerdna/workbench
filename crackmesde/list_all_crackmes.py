#!/usr/bin/python
# list all crackmes on crackmes.de
#
# HOW?
# watch what happens when you go to the archive:
# $ sudo tcpdump -s0 -A -i eth0 'tcp port 80 and host crackmes.de'
#
# POST /archive/ HTTP/1.1 
# Host: www.crackmes.de
# User-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:35.0) Gecko/20100101 Firefox/35.0
# Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8
# Accept-Language: en-US,en;q=0.5
# Accept-Encoding: gzip, deflate
# Referer: http://www.crackmes.de/archive/
# Cookie: PHPSESSID=jddcsqkvi4vidh5o2340q26c83; _ga=GA1.2.1908081374.1445613284; _gat=1
# Connection: keep-alive
# Content-Type: application/x-www-form-urlencoded
# Content-Length: 78
# 
# action=archive&start=40&title=&difficulty=0&platform=&lang=&type=ALL&sort=DATE

import re
import socket

hdrsFmt = 'POST /archive/ HTTP/1.1\x0d\x0aHost: www.crackmes.de\x0d\x0aUser-Agent: Mozilla/5.0 (X11; Ubuntu; Linux x86_64; rv:35.0) Gecko/20100101 Firefox/35.0\x0d\x0aAccept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\x0d\x0aAccept-Language: en-US,en;q=0.5\x0d\x0aAccept-Encoding: gzip, deflate\x0d\x0aReferer: http://www.crackmes.de/archive/\x0d\x0aCookie: PHPSESSID=jddcsqkvi4vidh5o2340q26c83; _ga=GA1.2.1908081374.1445613284; _gat=1\x0d\x0aConnection: keep-alive\x0d\x0aContent-Type: application/x-www-form-urlencoded\x0d\x0aContent-Length: %d\x0d\x0a\x0d\x0a'

reqFmt = 'action=archive&start=%d&title=&difficulty=0&platform=&lang=&type=ALL&sort=DATE'

curCrackme = 0
numCrackmes = 3000

while curCrackme < numCrackmes:
    # connect, send
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    sock.connect(('www.crackmes.de', 80))
    req = reqFmt % curCrackme
    hdrs = hdrsFmt % len(req)
    sock.send(hdrs + req)
    print "# getting crackmes [%d, %d] (of %d total)" % (curCrackme, curCrackme + 20, numCrackmes)

    # get all response, close
    resp = ''
    while 1:
        temp = sock.recv(4096)
        if not temp: break
        resp += temp
    sock.close()

    # parse the crackme url's
    # example:   <h2><a href="/users/mr.farshid/rzm_crack_me_crack_me_4_11/">RZM Crack Me - Crack Me 4 (11)</a> 
    for str in re.findall(r'^  <h2><a href="(.*)">.*</a> by ', resp, re.MULTILINE):
        print 'http://www.crackmes.de' + str    

    # loop
    curCrackme += 20


