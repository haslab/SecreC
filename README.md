# SecreC Analyser

#### Description:
[SecreC](https://github.com/sharemind-sdk/secrec) is a _Secure Multiparty Computation_ language developed by [Cybernetica](https://cyber.ee/en/), as part of the [Sharemind framework](https://github.com/sharemind-sdk).

The SecreC analyser is a self-contained static code analysis tool being developed by the [HasLab](http://haslab.uminho.pt/) that aims to increase the level of assurance awarded by the Sharemind system, by allowing application developers to verify, validate and optimize their high-level SecreC programs.

This tool takes a set of specific analysis flags, receives a SecreC program as input and returns an optimised and possibly annotated SecreC program as output. Its goal is to implement data flows and optimizations that go beyond the current analyses performed by the SecreC compiler, including state-of-the-art techniques from information flow type systems and optimisation of secure multiparty computation protocols.

#### Requirements:
* [Haskell Platform](https://www.haskell.org/platform/) (with GHC version 7.8.x)

#### Installation:
1. In the base directory, simply run the command
```
cabal install SecreC.cabal
````
2. Add the installation directory to your path, e.g., `~/.cabal/bin` or `./dist/build/secrec/secrec`

#### Usage:
For usage instructions, see
```
secrec --help
```

#### Examples:
Currently only the parser is functional.

To test the parser for a concrete program, you can invoke the tool with the typechecker disabled, e.g.:
```
> secrec examples/sign_x_y.sc --paths=stdlib/lib --tc=false
Modules sign_x_y, stdlib parsed.
```
