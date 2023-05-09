target remote localhost:12345

display/i $pc

set $i=0
break break_me
c

#source ~/.gdbinit

while ($i<100)
ni
set $i = $i + 1
end

quit
