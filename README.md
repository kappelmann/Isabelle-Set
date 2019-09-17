# Typed Set Theory

A formalization of set theory in Isabelle, with support for soft-types.

Build: [![CircleCI](https://circleci.com/bb/cezaryka/tyset.svg?style=svg&circle-token=2fc0576de43f1f1852e8500afc862e43da2ee1e5)](https://circleci.com/bb/cezaryka/tyset)

Goals:

* Provide type-based automation for specifications and proofs...
* ... based on an untyped formalism.
* Provide a Mizar compatibility layer, to match Mizar's style of working.
* Eventually be able to check the Mizar Mathematical Library.

## Structure and Dependencies

Directory `Isabelle/Mizar` contains the Isabelle/Mizar material, which mostly focuses on mimicking Mizar's style of working.
It allows the porting of some articles of the Mizar Mathematical Library (in Directory `MML`).

However, Mizar does not really abstract from the underlying set theory, which severely hinders automation, as it unfolds too many concepts.
Therefore, we attempt to provide a clean start in session/directory `Isabelle_Set`.
It contains a new development of Higher-Order Tarski Grothendieck Set Theory embedded in HOL.

 `Isabelle_Set` is used by `Isabelle/Mizar` for its notion of soft type. Ultimately, these developments should converge.


## How to build / run

This code currently depends on [the Isabelle repository](https://isabelle.in.tum.de/repos/isabelle),
which contains ongoing changes after the Isabelle2019 release. The file ISABELLE_VERSION specifies the exact revision, which
will also be used in the automated builds.

* Clone and build the Isabelle version, e.g.,

```
hg clone https://isabelle.in.tum.de/repos/isabelle isabelle-soft-types
cd isabelle-soft-types
hg up <REVISION>
```

* Follow the instructions in
[README_REPOSITORY](https://isabelle.in.tum.de/repos/isabelle/file/tip/README_REPOSITORY) to make prepare Isabelle.

* In this repo:

```
# Build supporting image
/path/to/isabelle-soft-types/bin/isabelle build -vRD .
```
```
# Build this development
/path/to/isabelle-soft-types/bin/isabelle build -vD .
```

## Automated builds

Automated builds can be found on CircleCI (https://circleci.com/bb/cezaryka/tyset).
There you can also configure email notifications for failed builds.


## Entry points

The whole development is still in a very experimental state. There are currently no examples that demonstrate all features in integration. The basic set theory can be used for formalizing concepts as usual, but the type system is not integrated yet.

Here are some good entry points for reading the sources:

File | Content 
-----|--------
`Soft_Types/Soft_Types_HOL.thy` | Notion of soft type (based on HOL): Types as predicates, Function types, intersections, adjectives. Tool setup
`Soft_Types/*.ML` | Infrastructure for soft types: Elaboration, Unification, Context data, etc.
`Isabelle_Set/Set_Theory_Axioms.thy` | Axiomatization of set theory
`Isabelle_Set/Set_Theory.thy` | Basics of Set Theory
`Isabelle_Set/{Pair,Relation,Function,Fixed_Points}.thy` | Further set-theoretic concepts
`Isabelle_Set/Structure.thy` | Basic syntax for structures
`Isabelle_Set/Set_Extension.thy` | Definitional set extension principle
`Isabelle_Set/Integer.thy` | Application of the extension principle to define ℤ ⊇ ℕ
`Isabelle_Set/Test_examples/Typing_Examples.thy` | Some examples of how soft type elaboration works, but mostly in the form of test cases.
`Isabelle_Set/Test_examples/Implicit_Args.thy` | Demonstrates automatic insertion of implicit arguments
`Isabelle_Set/Test_examples/Implicit_Assumptions.thy` | Demonstrates automatic generation of typing assumptions in the proof context.

