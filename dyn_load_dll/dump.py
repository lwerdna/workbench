fp = open('libfake.dll', 'rb')
data = fp.read()
fp.close()

print 'int libfake_len = %d;' % len(data) 
print 'unsigned char libfake[] = {'
print ','.join(map(lambda x: '0x%02X' % ord(x), list(data)))
print '};'

