# Typed Set Theory

A formalization of set theory in Isabelle, with support for soft-types.

Goals:

* Provide type-based automation for specifications and proofs...
* ... based on an untyped formalism.
* Provide a Mizar compatibility layer, to match Mizar's style of working.
* Eventualy be able to check the Mizar Mathematical Library.



## How to build

Compatibility: Isabelle 2018, Isabelle 2019 Release candidates

    # Build supporting image
	isabelle build -b HOL-Number_Theory
	
	# Build this development
	isabelle build -D .