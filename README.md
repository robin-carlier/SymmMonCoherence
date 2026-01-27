# SymmMonCoherence: coherences for symmetric monoidal categories in lean4

This repository contains a lean4 formalization of the fact that a symmetric monoidal category `C` may be viewed as a pseudofunctor `P : BurnsideFintype ⥤ᵖ Cat`, where `BurnsideFintype` is the (2,1)-category of spans of finite types (with isomorphisms of spans as 2-morphisms) such that the inclusions `const _ j : Unit ⟶ J` induce an equivalence of categories between `P.obj J` and the product category `J → C`. This interpretation of symmetric monoidal categories has been studied by Cranch in [his thesis](https://arxiv.org/abs/1011.3243) as a possible definition of symmetric monoidal infinity-categories.

The technical difficulty in this result is that pseudofunctors with the property above present symmetric monoidal categories in a highly unbiased way: the pseudofunctor encodes the data of tensor product functors in all arities and equips these functors with natural actions of the symmetric groups. On the other hand, the usual constructor for a symmetric monoidal category requires far less data: only the tensor product bifunctor, the unit, the structure isomorphisms, and only asks for a certain set of finite diagrams to commute. The key result needed to extend the low-arity data coherently to tensor products in every possible arities is Mac Lane’s coherence theorem for symmetric monoidal categories. This repository contains a formalization of that theorem as well, following ideas from [S. Piceghello’s thesis](https://nva.sikt.no/registration/0198f1714e08-ec2b3f03-26a6-4e26-a74b-10cf6c5e4903).

A small tour of the results involved in this construction is presented in the file `SymmMonCoherence.lean`.

## Key results in the repository

More specifically, here are selected facts and constructions formalized in this repository.
- The presentation of symmetric groups as Coxeter groups: this is in [`SymmMonCoherence/SymmetricGroupCoxeter.lean`](SymmMonCoherence/SymmetricGroupCoxeter.lean).
- A formalization of bicategories of spans: the basic definitions are in [`SymmMonCoherence/Spans/Basic.lean`](SymmMonCoherence/Spans/Basic.lean).
- A constructor for pseudofunctors out of the pith of bicategories of spans. This is in the directory [`SymmMonCoherence/Spans/PseudoFromBurnside`](SymmMonCoherence/Spans/PseudoFromBurnside).
- The construction of the free symmetric monoidal category on a type: this is in [`SymmMonCoherence/FreeSMC.lean`](SymmMonCoherence/FreeSMC.lean).
- The construction of the category of symmetric lists, a categorified version of multisets. This is in [`SymmMonCoherence/SList/Basic.lean`](SymmMonCoherence/SList/Basic.lean).
- The symmetric monoidal equivalence between symmetric lists and the free symmetric monoidal category. This is in [`SymmMonCoherence/SList/Equivalence.lean`](SymmMonCoherence/SList/Equivalence.lean).
- The link between morphisms of symmetric lists and permutations: this is in [`SymmMonCoherence/SList/Relations.lean`](SymmMonCoherence/SList/Relations.lean).
- Symmetric monoidal equivalences between categories of symmetric lists and various categories related to finite sets: this is in [`SymmMonCoherence/SList/Additive.lean`](SymmMonCoherence/SList/Additive.lean).
- The Kleisli bicategory for the relative pseudomonad of symmetric lists: this is in [`SymmMonCoherence/SList/Kleisli.lean`](SymmMonCoherence/SList/Kleisli.lean).
- The pseudofunctor out of `BurnsideFintype` attached to a symmetric monoidal category is defined in the directory [`SymmMonCoherence/SList/ToPseudofunctor`](SymmMonCoherence/SList/ToPseudofunctor).

## Paper
Yet to come.
