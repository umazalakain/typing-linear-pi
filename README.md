
A mechanisation of the linear π-calculus that uses leftover typing and is based on a set of partial commutative monoids.
The related paper can be found [here](paper).

[paper]: https://arxiv.org/abs/2005.05902

# Compilation

This project has been tested with Agda 2.6.1.1 and Agda-Stdlib 1.4.
You can typecheck the entire project as follows:

    agda -i . --safe Everything.agda

# Layout

The untyped syntax and semantics are defined in `PiCalculus.Syntax` and `PiCalculus.Semantics`, respectively.
The type system is based on a set of multiplicity algebras, for which the interface is defined in `PiCalculus.LinearTypeSystem.Algebras`.
Examples of such algebras are found in `PiCalculus.LinearTypeSystem.Algebras.*`.
The type system defined on top of them is in `PiCalculus.LinearTypeSystem`.
Example derivations can be found in `PiCalculus.Examples`.
Subject reduction is proven in `PiCalculus.LinearTypeSystem.SubjectReduction`.
