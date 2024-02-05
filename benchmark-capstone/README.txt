NEW TESTS (Apple M3 Pro)

./method0 cs_disasm()                    3.7e6 instrs/sec or 19.3 minutes to do all instructions
./method1 cs_disasm_iter()               3.9e6 instrs/sec or 18.3 minutes
./method2 py ->ctypes-> cs_disasm_iter() 2.2e6 instrs/sec or 33.5 minutes
./method3 py disasm_lite()                .5e6 instrs/sec or 65.0 minutes

OLD TESTS (Some X86_64 MacBook Pro):

method0: cs_disasm()
         1,300,000 instrs/sec

method1: cs_disasm_iter()
         1,500,000 instrs/sec

method2: py -ctypes-> cs_disasm_iter()
          500,000 instrs/sec

method3: py disasm_lite()
          100,000 instrs/sec

make
./run.sh
