# Typed Set Theory

A formalization of set theory in Isabelle, with support for soft-types.

Build: [![CircleCI](https://circleci.com/bb/cezaryka/tyset.svg?style=svg&circle-token=2fc0576de43f1f1852e8500afc862e43da2ee1e5)](https://circleci.com/bb/cezaryka/tyset)

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

	
## Automated builds

Automated builds can be found on CircleCI (https://circleci.com/bb/cezaryka/tyset).
There you can also configure email notifications for failed builds.