./test0.py - register a workflow that prints "Hello" during basic block analysis
./test1.py - graph the workflow topology
./topology.png - resulting graph from test1.py
./test2.py - workflow that prints "Hello" after IL is lifted (at "resetIndirectBranchesOnFullUpdate")
./test3.py - generate c++ so every single point in the workflow system is hooked
./fullhook - the generated workflow that prints at every location possible in the workflow system
