import sys, re, os, subprocess

PATH = "c:/Program Files (x86)/Windows Kits/10/Lib/10.0.17134.0/um/x64"

blacklist = {'if', 'rgEDBGGlobals', 'utf8_countTrailBytes', 'mi_clientFT_V1',
'DnsGlobals', 'NdrTypeFlags', 'SimpleTypeAlignment', 'SimpleTypeBufferSize',
'SimpleTypeMemorySize', 'LdrSystemDllInitBlock', 'g_hHeapMalloc',
'DxTrimNotificationListHead', 'GdiBatchLimit', 'LpkEditControl',
'LpkpEditControlSize', 'fpClosePrinter', 'gMaxGdiHandleCount', 'gW32PID',
'g_systemCallFilterId', 'ghICM', 'pGdiDevCaps', 'pGdiSharedHandleTable',
'pGdiSharedMemory', 'semDxTrimNotification', 'g_rgSCardRawPci',
'g_rgSCardT0Pci', 'g_rgSCardT1Pci', 'sqlite3_data_directory',
'sqlite3_temp_directory', 'sqlite3_version'}

def is_cpp(sym_name):
	if sym_name.startswith('?'):
		return True
	if '@@' in sym_name:
		return True
	if '::' in sym_name:
		return True
	return False

def get_lib_exports(fpath):
	output = subprocess.check_output(['dumpbin', '/EXPORTS', fpath])
	output = output.decode('utf-8')
	exports = []
	capture = False
	for line in output.splitlines():
		line = line.strip()
		if line == 'Summary':
			break
		elif 'ordinal' in line and 'name' in line:
			capture = True
		elif line and capture:
			# filter out ordinal number
			if re.match(r'^\d+', line):
				line = re.match(r'^\d+\s*(.*)', line).group(1)
			sym_name = line
			if not is_cpp(sym_name) and not sym_name in blacklist:
				exports.append(sym_name)
	return exports

fnames = [x for x in os.listdir(PATH) if x.endswith('.lib')]

database = {}

for fname in fnames:
	fpath = os.path.join(PATH, fname)
	database[fpath] = get_lib_exports(fpath)

# generate C
if sys.argv[1] in ['c', 'C']:
	for (fpath, exports) in database.items():
		print(f'// {fpath} has {len(exports)} exports')
		for export in exports:
			print(f'void {export}();')

	print('''
	int main(int ac, char **av)
	{
	''')

	for (fpath, exports) in database.items():
		print(f'	// {fpath}')
		for export in exports:
			print(f'	{export}();')

	print('''
		return 0;
	}
	''')
# generate makefile or build.bat
elif sys.argv[1] in ['make', 'Make', 'makefile', 'Makefile']:
	print('cl /c test.c')

	libs = database.keys()
	libs = [fpath for fpath in libs if len(database[fpath])]
	libs = [os.path.basename(fpath) for fpath in libs]
	print('link test.obj ' + ' '.join(libs))
