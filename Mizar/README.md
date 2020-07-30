# Isabelle/Mizar
## Structure and Dependencies

This work focuses on mimicking Mizar's style of working in Isabelle/HOL.
It allows the porting of some articles of the Mizar Mathematical Library (in Directory `MML`).

However, Mizar does not really abstract from the underlying set theory, which severely hinders automation, as it unfolds too many concepts.
A clean start of a modern appraoch to softly-typed set theory can be found in the other folders of this repository.

The `Soft_Types` session is used by `Isabelle/Mizar` for its notion of soft type.

## Goals
* Provide type-based automation for specifications and proofs...
* ... based on an untyped formalism.
* Provide a Mizar compatibility layer, to match Mizar's style of working.
* Eventually be able to check the Mizar Mathematical Library.
