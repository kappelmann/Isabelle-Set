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

Ultimately, these developments should converge.

Allowed Dependencies: `Isabelle_Set` and `Isabelle/Mizar` remain independent. They may introduce a similar notion of soft type at some point.


## How to build / run

This code currently depends on a [custom clone of the Isabelle repository](https://bitbucket.org/akrauss/isabelle-soft-types),
which contains some experimental changes to Isabelle. The file ISABELLE_VERSION specifies the exact revision, which
will also be used in the automated builds.

* Clone and build the Isabelle version, e.g.,

    hg clone https://bitbucket.org/akrauss/isabelle-soft-types
    cd isabelle-soft-types
    hg up <REVISION>

* Follow the instructions in
[README_REPOSITORY](https://isabelle.in.tum.de/repos/isabelle/file/tip/README_REPOSITORY) to make prepare Isabelle.

* This repo:

    # Build supporting image
    /path/to/isabelle-soft-types/bin/isabelle build -b HOL-Number_Theory
    
    # Build this development
    /path/to/isabelle-soft-types/bin/isabelle build -D .


## Automated builds

Automated builds can be found on CircleCI (https://circleci.com/bb/cezaryka/tyset).
There you can also configure email notifications for failed builds.