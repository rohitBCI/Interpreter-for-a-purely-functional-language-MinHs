# Interpreter-for-a-purely-functional-language-MinHs
Implemented an interpreter for the Haskell like langauge MinHs using an environment semantics, including support for recursion and closures

# Building minhs
minhs (the compiler/abstract machine) is written in Haskell, and requires the stack tool

## Building with stack

Build the compiler by simply invoking:

$ stack build

To see the debugging options, run (after building):

$ stack exec minhs-1

To run the compiler with a particular file, run:

$ stack exec minhs-1 foo.mhs

To run all  tests, type:

$ ./run_tests_stack.sh
