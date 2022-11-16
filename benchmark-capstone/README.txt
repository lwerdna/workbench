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
