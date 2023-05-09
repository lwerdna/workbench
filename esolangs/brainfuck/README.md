## using bfbasic

```
git clone https://github.com/mzattera/bfbasic
cd bfbasic/bfbasic/src
javac AlgebraicExpression.java
javac Variables.java
javac bfbasic.java
java bfbasic ../examples/99bob.bas -o 99bob.bf
```

## using BrainfuckAsmCompiler

```
git clone https://github.com/esovm/BrainfuckAsmCompiler.git
chmod +x ./build.sh
./build.sh
cd build
cd ..
java -cp build Main samples/fibonacci.asm -o ./fibonacci.bf
```

where `-cp` specifies class path for java





