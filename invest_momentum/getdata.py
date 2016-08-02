#!/usr/local/bin/python

import re
import urllib2

# to test, substitute a symbol here in 
# http://ichart.finance.yahoo.com/table.csv?s=<sym>
syms = ['SPY', 'XLE', 'XLU', 'XLK', 'XLB', 'XLP', 'XLY', 'XLI', 'XLV', 'XLF',
    'VNQ', 'VEA', 'VWO', 'BND', 'V', 'AMZN']


def downloadData():
    for sym in syms:
        url = "http://ichart.finance.yahoo.com/table.csv?s=%s" % sym
        print "calling urlopen()..."
        data = urllib2.urlopen(url).read()
        
        fname = '%s.csv' % sym
        print "writing %d bytes to %s" % (len(data), fname);
        fobj = open(fname, 'w')
        fobj.write(data)
        fobj.close()

def parseData(sym):
    date2data = {}

    fname = '%s.csv' % sym
    fobj = open(fname, 'r')
    lines = fobj.readlines()
    fobj.close()

    for line in lines[1:]:
        fields = line.split(',')
        [date, open_, high, low, close, volume, adjclose] = fields
        #print "adding key %s\n" % date
        date2data[date] = {'open':open_, 'high':high, 'low':low, 'close':close,
            'volume':volume, 'adjclose':adjclose.strip()}
    
    return date2data

def spreadsheetClosingLine():
    for sym in syms:
        data = parseData(sym)

        key = '2016-06-01'
        if not key in data:
            key = '2016-06-02'
            #key = '2016-04-29'
        print '%.02f,' % round(float(data[key]['adjclose']), 2),
            
