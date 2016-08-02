#!/usr/local/bin/python

import re
import sys
import urllib2
import datetime

# to test, substitute a symbol here in 
# http://ichart.finance.yahoo.com/table.csv?s=<sym>
syms = ['SPY', 'XLE', 'XLU', 'XLK', 'XLB', 'XLP', 'XLY', 'XLI', 'XLV', 'XLF',
    'VNQ', 'VEA', 'VWO', 'BND', 'V', 'AMZN']

data = {}

###############################################################################
# UTILS
###############################################################################

def dateDaysInMonth(month, year):
    daysInMonth = [0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    # if leap year, feb has 29
    if(year % 4 == 0):
        daysInMonth[2] = 29

    return daysInMonth[month]

def dateDecrDay(date):
    (y,m,d) = map(int, date.split('-'))

    # try decr day
    if d == 1:
        # can decr mo?
        if m == 1:
            # no, decr year
            y -= 1
            m = 12
            d = dateDaysInMonth(m, y)
        else:
        # yes, decr month
            m -= 1
            d = dateDaysInMonth(m, y)
    else:
        d -= 1

    return '%04d-%02d-%02d' % (y,m,d)

def dateIncrDay(date):
    (y,m,d) = map(int, date.split('-'))

    # can incr day?
    if d == dateDaysInMonth(m, y):
        # can incr month?
        if m == 12:
            # no, incr year
            y += 1
            m = 1
            d = 1
        else:
        # yes, incr month
            m += 1
            d = 1
    else:
        d += 1

    return '%04d-%02d-%02d' % (y,m,d)

def dateDecrMonth(date):
    (y,m,d) = map(int, date.split('-'))

    if m == 1:
        y -= 1
        m = 12
        # handle case where, example: March 31 gets decremented to Feb 31
        if d > dateDaysInMonth(m, y):
            d = dateDaysInMonth(m, y);
    else:
        m -= 1

    return '%04d-%02d-%02d' % (y,m,d)

def dateIncrMonth(date):
    (y,m,d) = map(int, date.split('-'))

    if m == 12:
        y += 1
        m = 1
        # handle case where, example: Jan 31 gets incremented to Feb 31
        if d > dateDaysInMonth(m, y):
            d = dateDaysInMonth(m, y);
    else:
        m += 1

    return '%04d-%02d-%02d' % (y,m,d)

def dateGetCurMonthStart():
    now = datetime.datetime.now()
    return '%04d-%02d-01' % (now.year, now.month)

###############################################################################
# ACQUIRING, PARSING THE STOCK DATA
###############################################################################

def downloadData():
    global syms
    for sym in syms:
        url = "http://ichart.finance.yahoo.com/table.csv?s=%s" % sym
        print "calling urlopen()..."
        data = urllib2.urlopen(url).read()
        
        fname = '%s.csv' % sym
        print "writing %d bytes to %s" % (len(data), fname);
        fobj = open(fname, 'w')
        fobj.write(data)
        fobj.close()

def parseData():
    global data

    for sym in syms:
        date2cols = {}

        fname = '%s.csv' % sym
        print "loading %s..." % fname,
        fobj = open(fname, 'r')
        lines = fobj.readlines()
        fobj.close()
        print "%d records found, " % len(lines),
    
        # discard first line (column headers) and keep the next two years
        lines = lines[1:(3*365)]
        print "%d records read" % len(lines)
        for line in lines:
            fields = line.split(',')
            [date, open_, high, low, close, volume, adjclose] = fields
            #print "adding key %s\n" % date
            date2cols[date] = {'open':open_, 'high':high, 'low':low, 'close':close,
                'volume':volume, 'adjclose':adjclose.strip()}
       
        # horrible hack, but yahoo leaves out many days, and I'm not sure why
        # 'fill it forward' starting at the oldest date
        dateOldest = lines[-1].split(',')[0]
        dateNewest = lines[0].split(',')[0]
        dateCur = dateOldest
        replaceDate = None
        replaceData = None
        while dateCur != dateNewest:
            if dateCur in date2cols:
                replaceDate = dateCur
                replaceData = date2cols[dateCur]
            else:
                print "%s: %s was missing, so inserted data from %s" % \
                    (sym, dateCur, replaceDate)
                date2cols[dateCur] = replaceData
            dateCur = dateIncrDay(dateCur)

        data[sym] = date2cols

# append extra shit to data, like the 1month change, 3month change, etc
#def augment():
#    for sym in syms:
        
def spreadsheetClosingLine():
    global data
    if not data:
        parseData()

    for sym in syms:
        date2cols = data[sym]

        dateStr = dateGetCurMonthStart()
        #if not key in data:
        #    key = '2016-06-02'
        #    #key = '2016-04-29'
        print '%.02f,' % (100*float(date2cols[dateStr]['adjclose']))

def fullReport():
    global data
    if not data:
        parseData()


    moStart = '2014-10-01'
    #moStart = dateGetCurMonthStart()
    #for i in range(12):
    #    moStart = dateDecrMonth(moStart)

    print 'Prices'
    print '------'

    print ' '*10,
    for sym in syms:
        print "% 7s" % sym,
    print ''

    moCur = moStart
    for i in range(12+1):
        print moCur,

        for sym in syms:
            date2cols = data[sym]
            priceThisMonth = float(date2cols[moCur]['adjclose'])
            print "{:7.2f}".format(priceThisMonth),

        print ''
        moCur = dateIncrMonth(moCur)

    print ''
    print '1 Month Changes'
    print '---------------'

    print ' '*10,
    for sym in syms:
        print "% 7s" % sym,
    print ''

    moCur = moStart
    for i in range(12+1):
        print moCur,

        for sym in syms:
            date2cols = data[sym]
            priceThisMonth = float(date2cols[moCur]['adjclose'])
            priceLastMonth = float(date2cols[dateDecrMonth(moCur)]['adjclose'])
            percentChange = (priceThisMonth - priceLastMonth)/priceLastMonth;
            print "{:6.2f}%".format(100*percentChange),

        print ''
        moCur = dateIncrMonth(moCur)

###############################################################################
# TESTS, MAIN
###############################################################################
def test():
    print "TESTING 20 YEARS OF DAILY INCREMENTING"
    print "======================================"
    tmp = '1990-01-01'
    up = []
    for i in range(20*365):
        up.append(tmp)
        tmp = dateIncrDay(tmp)

    tmp = up[-1]
    down = []
    for i in range(20*365):
        down.append(tmp)
        tmp = dateDecrDay(tmp)

    down.reverse()
    if up == down:
        print "OK"
    else:
        print "ERROR!"

    print "TESTING 20 YEARS OF MONTHLY INCREMENTING"
    print "========================================"
    tmp = '1990-01-01'
    up = []
    for i in range(20*12):
        up.append(tmp)
        tmp = dateIncrMonth(tmp)

    tmp = up[-1]
    down = []
    for i in range(20*12):
        down.append(tmp)
        tmp = dateDecrMonth(tmp)

    down.reverse()
    if up == down:
        print "OK"
    else:
        print "ERROR!"
