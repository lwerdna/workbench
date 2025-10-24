#!/usr/bin/env python

import re
import sys
import glob
import time
import pprint
import serial # pip install pyserial

import helpers

# parses according to 3GPP TS 27.007
#
# example input is:
# '+COPS: (1,"Verizon","Verizon","311480",12),,(0-4),(0-2)'
def parse(string):
    seen_supported_modes = False
    avail_to_str = {'0':'unknown', '1':'available', '2':'current', '3':'forbidden'}
    act_to_str = {'0':'GSM', '1':'GSM Compact', '2':'UTRAN', '3':'GSM w/EGPRS (EDGE)', '4':'UTRAN w/HSDPA', '5':'UTRAN w/HSUPA', '6':'UTRAN w/HSDPA & HSUPA (HSPA)', '7':'E-UTRAN (LTE)', '8':'E-UTRAN (LTE Cat-M1 / eMTC)', '9':'NR (5G New RAdio)', '10':'E-UTRAN (LTE w/ other extensions)', '11':'E-UTRAN (LTE Cat-M1 + NB-IoT hybrid)', '12':'E-UTRAN (LTE Cat-NB1 / NB-IoT)', '13':'E-UTRAN (unused in many firmwares)', '14':'NG-RAN (5G NR Cat-MTC / RedCap)', '15':'NG-RAN (future extensions / reserved)'}
    act_to_notes = {'0':'5G (basic)', '1':'Rare/legacy', '2':'3G WCDMA', '3':'2.5G', '4':'3.5G', '5':'3.5G', '6':'Full HSPA', '7':'4G LTE', '8':'LTE-M (IoT profile)', '9':'5G (NSA/SA depending on mode)', '10':'Rare, vendor-specific', '11':'Seen on some Qualcomm/Quectel', '12':'NB-IoT (Narrowband IoT)', '13':'Reserved / vendor-specific', '14':'5G Reduced-Capability (Rel-17/18)', '15':'Reserved'}

    chunks = []
    while True:
        while string and not string.startswith('('):
            string = string[1:]
        if not string:
            break
        chunk = string[0:string.find(')')+1]
        chunks.append(chunk)
        string = string[len(chunk):]

    for chunk in chunks:
        if m := re.match(r'\((.*), (.*), (.*), (.*), (.*)\)', chunk):
            availability, long_oper_name, short_oper_name, plmn_id, access_tech = m.group(1,2,3,4,5)
            print(f'availability: {availability} ({avail_to_str[availability]})')
            print(f'operator name (long): {long_oper_name}')
            print(f'operator name (short): {short_oper_name}')
            print(f'PLMN: {plmn_id}')
            print(f'access technology: {access_tech} ({act_to_str.get(access_tech, "unknown")}) ({act_to_notes.get(access_tech, "unknown")})')
        elif m := re.match(r'\((\d+)-(\d+)\)', chunk):
            if not seen_supported_modes:
                print(f'supported modes: {chunk} (0=automatic, 1=manual, 2=deregister, 3=setonly, 4=manual/automatic)')
                seen_supported_modes = True
            else:
                print(f'range of access technology values: {chunk} (0=GSM, 1=GSM compact, 2=UTRAN/UMTS, 7=LTE, 9=NR5G)')

    pprint.pprint(chunks)
    return

if __name__ == '__main__':
    fpath = sys.argv[1]

    response = helpers.open_modem_send_command(fpath, 'AT+COPS=?\r', timeout=4*60)

    parse(response)
    #response = helpers.open_modem_send_command(fpath, 'AT\r')
    print(response)

    
