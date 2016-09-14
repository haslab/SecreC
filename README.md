# SecreC Analyser

#### Description:
[SecreC](https://github.com/sharemind-sdk/secrec) is a _Secure Multiparty Computation_ language developed by [Cybernetica](https://cyber.ee/en/), as part of the [Sharemind framework](https://github.com/sharemind-sdk).

The SecreC analyser is a self-contained static code analysis tool being developed by the [HasLab](http://haslab.uminho.pt/) that aims to increase the level of assurance awarded by the Sharemind system, by allowing application developers to verify, validate and optimize their high-level SecreC programs.

This tool takes a set of specific analysis and transformation flags, receives a (possibly annotated) SecreC program as input and returns a transformed SecreC program as output. Its goal is to implement data flows and optimizations that go beyond the current analyses performed by the SecreC compiler, including state-of-the-art techniques from information flow type systems and optimisation of secure multiparty computation protocols. It currently supports typechecking, simplification and verification of SecreC programs.

A programmer interacts with the SecreC analyser in the same way as with a typical compiler: as the tool produces errors, and the programmer responds by changing the program, including its security types and specifications.

#### Requirements:
* [Haskell Platform](https://www.haskell.org/platform/) (with GHC version 7.8.x)
* [Dafny](https://dafny.codeplex.com/) (only for verification)
* [Boogie](https://boogie.codeplex.com/) (only for verification)
* [Z3](https://z3.codeplex.com/) (only for verification)

#### Installation:
1. Install each package `xyz` from the `packages` directory
```
cd xyz
cabal install xyz.cabal
cd ..
```
2. After installing all package dependencies, install the base package
```
cabal install SecreC.cabal
```
3. Add the installation directory to your path, e.g., `~/.cabal/bin` or `./dist/build/secrec/secrec`

#### Installation with cabal sandbox

Alternatively, cabal sandboxes can be used as follows.
First we have to initialize and update the git submodules.
```
git submodule init
git submodule update
```

Next use cabal to build the analysis tool.
```
cabal sandbox init
cabal sandbox add-source packages/*
cabal install --only-dependencies -j
cabal configure
cabal build -j
cabal install
```

The `secrec` binary can be found under `.cabal-sandbox/bin`.

#### Usage:
For usage instructions, see
```
secrec --help
```

#### Tests:
Before testing make sure that you have packages 'hspec', 'hspec-core' and 'hspec-contrib' installed:
```
cabal install hspec
cabal install hspec-core
cabal install hspec-contrib
```

To run the SecreC regression tests with nice output, you can invoke:
````
runhaskell tests/Tests.hs
```

#### Examples:

By default, the tool will typecheck a given SecreC program:
```
> secrec tests/regressions/arrays/00-trivia.sc
Modules builtin, main are well-typed.
```

To verify the security properties of a SecreC program, you can invoke the tool with the `verify` flag:
```
> secrec examples/leakage/cut/cut.sc --verify
Modules builtin, axioms, cut are well-typed.
...
Verified 30 functional properties with 0 errors.
Verified 38 leakage properties with 0 errors.
```

You can verify particular procedures by initializing the `entrypoints` flag, e.g.:
```
secrec examples/leakage/cut/cut.sc --verify --entrypoints="cut"
```

