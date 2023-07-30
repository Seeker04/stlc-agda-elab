# Agda formalisation of an elaborator for a language based on simply typed lambda calculus

## Abstract

Programming languages are the backbone of software development. Defining them with mathematical rigorousness in a formal framework can help us better understand and reason about them. One way of explaining languages is through the process of elaboration. It refines the concept of the language from broader ideas such as strings and lexical tokens to more concrete and strict ones like syntax trees and well-typed terms.

This paper aims to walk the reader through each step of such an elaboration. Our method is an extension to an existing formalisation of a simple language. We go from source code by lexical analysis to a list of tokens, then by parsing to an abstract syntax tree, which is followed by scope checking leading to an abstract binding tree. Finally, we present a bidirectional type checking algorithm which turns the binding tree to a well-typed term of our language. We apply a correct by construction approach by 1.) formalising all levels and the algorithms between them in type theory using Agda, 2.) constructing terms with an algebraic description, which cannot be badly typed by definition.

Our language is based on simply typed lambda calculus with the function space having finite types: booleans, nullary and binary products and sums; inductive types: naturals, lists, trees (and their iterators); coinductive types: streams and machines; and a few additional operators.

We discuss both the benefits and difficulties of the presented solution and compare it to other approaches. The study is concluded by ideas on how our framework can be extended or improved.

**Keywords:** lambda-calculus, Agda, formalisation, elaboration, parsing, typechecking

## About

This project started as an extension to an existing formalisation. The well-typed description, also quotiented by equations, that you can see in [STLC.agda](src/STLC.agda) was written by Ambrus Kaposi [here](https://bitbucket.org/akaposi/typesystems/src/master/).

If you wish to see the commits of the elaborator from before going independent, you can find them [in this fork](https://bitbucket.org/zahoranb/typesystems/commits/).

You can read the paper (my MSc thesis) in [STLC-elaboration-in-Agda.pdf](paper/STLC-elaboration-in-Agda.pdf) and browse the source code in [src](src).

## Installation

This project requires [Agda version 2.6.2.2](https://wiki.portal.chalmers.se/agda/Main/Download) and the following libraries:

* [agda-stdlib-1.7.1](https://github.com/agda/agda-stdlib/releases)
* [agdarsec-0.5.0](https://github.com/gallais/agdarsec/releases)

1. Make sure to download the correct versions, i.e., `1.7.1` and `0.5.0`, respectively!

2. Follow the steps of the [stdlib install guide](https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md)

3. Also, add the agdarsec path next to the stdlib one in your `$HOME/.agda/libraries`:
```
<download-location>/agda-stdlib-1.7.1/standard-library.agda-lib
<download-location>/agdarsec-0.5.0/agdarsec.agda-lib
```

Now you should be able to typecheck the project.

