target remote localhost:12345
b android_dlopen_ext
#c
#
#b *0xb6fa4a4e
#commands
#echo load_library() calls soinfo_alloc()
#x/s $r1
#end
#
#b *0xb6fa4a86
#commands
#echo load_library() calls elfreader::read()
#end
#
#b *0xb6fa7e4e
#commands
#echo "elfreader::read() calls ReadElfHeader()"
#end
#
#b *0xb6fa7e58
#commands
#echo "elfreader::read() calls ReadProgramHeaders()"
#end
#
#b *0xb6fa7e62
#commands
#echo "elfreader::read() calls ReadSectionHeaders()"
#end

source ~/.gdbinit
