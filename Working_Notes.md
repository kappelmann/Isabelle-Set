# Working notes for Isabelle/Set

**Formulating a concept as a set vs. a soft type**
Proper classes and type classes should be soft types. For everything else, try to default to sets, except when you have a good reason.

**Set-theoretic vs. HOL functions**
These are usually easily interconvertible; however note that structures are implemented as sets, so any function field of a structure has to be set-theoretic.
