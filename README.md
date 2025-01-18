# Verified Compiler

This is a toy example of a verified compiler. 
It starts from a "high-level" language of natural numbers, Booleans, conditional statements, and conjunction.
The compilation target is a stack machine over natural numbers with instructions for pushing constants, performing conjunction, as well as conditional and unconditional jumps forward.
The compiler performs a restricted form of constant folding on the high-level language before lowering terms to stack machine programs.
We show that the compiler is semantics preserving by proving that evaluation of high-level terms produces an equivalent result to executing the corresponding stack machine.

