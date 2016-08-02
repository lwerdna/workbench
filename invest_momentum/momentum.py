#!/usr/local/bin/python

import re
import sys
import urllib2
import datetime

# to test, substitute a symbol here in 
# http://ichart.finance.yahoo.com/table.csv?s=<sym>
syms = ['SPY', 'XLE', 'XLU', 'XLK', 'XLB', 'XLP', 'XLY', 'XLI', 'XLV', 'XLF',
    'VNQ', 'VEA', 'VWO', 'BND', 'V', 'AMZN']

#costCol = 'Adj Close'
costCol = 'Close'
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

def dateDecrMonth(date, amt=1):
    (y,m,d) = map(int, date.split('-'))

    for i in range(amt):
        if m == 1:
            y -= 1
            m = 12
            # handle case where, example: March 31 gets decremented to Feb 31
            if d > dateDaysInMonth(m, y):
                d = dateDaysInMonth(m, y);
        else:
            m -= 1

    return '%04d-%02d-%02d' % (y,m,d)

def dateIncrMonth(date, amt=1):
    (y,m,d) = map(int, date.split('-'))

    for i in range(amt):
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
            date = fields[0]
            fields = map(float, fields[1:])
            [open_, high, low, close, volume, adjclose] = fields
            #print "adding key %s\n" % date
            date2cols[date] = {'Open':open_, 'High':high, 'Low':low, 'Close':close,
                'Volume':volume, 'Adj Close':adjclose}
       
        # horrible hack, but yahoo leaves out many days, and I'm not sure why
        # use strategy 'fill it forward' starting at the oldest date
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
        print '%.02f,' % (100*date2cols[dateStr][costCol])

def reportMonthHistoryTable(dateStart, dateEnd, col, title, asPercent=False):
    global data
    if not data:
        parseData()

    # print the table title
    print ''
    print title
    print '-' * len(title)

    # print the symbols as columns
    print ' '*10,
    for sym in syms:
        print "% 7s" % sym,
    print ''

    # outer loop (rows) are the dates
    dateCur = dateStart
    while 1:
        print dateCur,

        # inner loop (cols) are the value
        for sym in syms:
            value = data[sym][dateCur][col]
            if asPercent:
                print "{:6.2f}%".format(100*value),
            else:
                print "{:7.2f}".format(value),

        # next row
        print ''

        # quit?
        if dateCur == dateEnd:
            break
        dateCur = dateIncrMonth(dateCur)


def fullReport():
    global data
    if not data:
        parseData()

    moNow = dateGetCurMonthStart()

    # annotate the data for the last 12 months, adding keys for 1, 3, and 12
    # month changes
    for sym in syms:
        date2cols = data[sym]
    
        # starting this month
        moCur = moNow

        # go back 24 months
        for i in range(24):
            mo1ago = dateDecrMonth(moCur, 1)
            mo3ago = dateDecrMonth(moCur, 3)
            mo6ago = dateDecrMonth(moCur, 6)
            mo12ago = dateDecrMonth(moCur, 12)

            if (not moCur in date2cols) or (not mo1ago in date2cols) \
              or (not mo3ago in date2cols) or (not mo6ago in date2cols) \
              or (not mo12ago in date2cols):
                raise "missing data!"

            priceNow = date2cols[moCur][costCol]
            price1ago = date2cols[mo1ago][costCol]
            price3ago = date2cols[mo3ago][costCol]
            price6ago = date2cols[mo6ago][costCol]
            price12ago = date2cols[mo12ago][costCol]
            
            change1 = (priceNow - price1ago) / price1ago
            change3 = (priceNow - price3ago) / price3ago 
            change6 = (priceNow - price6ago) / price6ago
            change12 = (priceNow - price12ago) / price12ago

            date2cols[moCur]['change1mo'] = change1
            date2cols[moCur]['change3mo'] = change3
            date2cols[moCur]['change6mo'] = change6
            date2cols[moCur]['change12mo'] = change12
            date2cols[moCur]['changeAvg'] = (change1+change3+change6+change12)/4

            #print "setting %s on %s to [%f, %f, %f]" % \
            #    (sym, moCur, change1, change3, change12)

            # next
            moCur = dateDecrMonth(moCur)

    moStart = '2014-10-01'

    reportMonthHistoryTable(moStart, moNow, costCol, 'prices')
    reportMonthHistoryTable(moStart, moNow, 'change1mo', 'delta (vs. 1 month prior)', True)
    reportMonthHistoryTable(moStart, moNow, 'change3mo', 'delta (vs. 3 months prior)', True)
    reportMonthHistoryTable(moStart, moNow, 'change6mo', 'delta (vs. 6 months prior)', True)
    reportMonthHistoryTable(moStart, moNow, 'change12mo', 'delta (vs. 12 months prior)', True)
    reportMonthHistoryTable(moStart, moNow, 'changeAvg', '"momentum" (avg. of 1,3,6,12 month deltas)', True)

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
