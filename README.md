# Coq sample theorems

This repository showcases a collection of simple theorems proved using Coq,
compiled as part of the author's education in automated theorem proving.
The files in this repository are derived from materials originally sourced from
Adam Chlipala's Certified Programming with Dependent Types,
the Coq tutorial presented at ITP 2015 (https://coq.inria.fr/coq-itp-2015),
and the Advanced Functional Programming course at the University of Warsaw,
taught by Dr. Daria Walukiewicz-Chrząszcz.

Notably, the file [DependentVectorTheorems.v](DependentVectorTheorems.v) contains a proof
that employs the Uniqueness of Identity Proofs (UIP) axiom to demonstrate theorems
based on equality. However, it is now widely recognized that the UIP axiom should be
rejected, as it is incompatible with the univalence principle from homotopy
type theory (HoTT), which is an essential framework for modern type theory.

Another interesting file to look at is [Kolmogorov.v](Kolmogorov.v), which contains
a formalization of Kolmogorov's beautiful theorem about the equivalence between the
provability of a formula in classical logic and the provability of its double negation
translation in intuitionistic logic.