---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
---

# Decomposition of Persistence Modules

The objective of this repository is to formalise the statement of the barcode decomposition theorem of persistence modules into the Lean proof assistant. 

Formalisation is the process by which mathematical definitions, theorems and results are typed into a computer proof assistant - a program which knows the axioms of mathematics and is capable of checking the validity of proofs. Lean is one such program, and an extensive amount of mathematics has already been formalised into it. 


## Source

The main source for our work is the paper "Decomposition of Persistence Modules" authored by Professors Magnus Bakke Botnan and William Crawley-Boevey and published in 2019. This paper is available [here](https://arxiv.org/pdf/1811.08946).

The main result we currently aim to prove is Theorem 1.1: *Any pointwise finite-dimensional persistence module (over a small category) is a direct sum of indecomposable modules with local endomorphism ring*. This theorem is an improvement over Professor William Crawley-Boevey's [2015 result](https://arxiv.org/abs/1210.0819), which held for persistence modules over a totally ordered indexing set. This was itself a large improvement over prior results, which only held for few indexing sets (finite sets, the integers, the reals...). 

## Contents

The code is contained in the directory `PH_formalisation`. It contains the following subdirectories: 
* `Mathlib`: contains material missing from current files in Mathlib. 
* `Prereqs`: contains basic definitions and properties of persistence modules.

In addition, we also have the following files: 
* `DirectSumDecomposition`: defines direct sum decompositions of persistence modules and proves basic facts about them. 
* `DirectSumDecompositionDual`: provides the same structures, equipped with the dual order. 
* `EndoRingIsLocal`: proves that indecomposable modules have local endomorphism rings. 
* `MaximalDecompExists`: proves that pointwise finite-dimensional persistence modules decompose as a direct sum of indecomposable modules.
* `BumpFunctor`: contains code generalising the notion of interval modules to other categories. 


### Current progress

The project is not yet finished. The following table details live which files are unfinished, and
how many 'sorries' (unproven statements) remain in each file.

{% include sorries.md %}

## Future Considerations

Once Theorem 1.1 is proven, we hope to be able to prove Theorem 1.2: *Pointwise finite-dimensional persistence modules over a totally ordered set decompose into interval modules*. This result is frequently used in topological data analysis, and hence it should be upstreamed to mathlib.

The current implementation views persistence modules and persistence submodules as purely separate objects. It should be a future goal to unify them.

On top of the new developments, there are many basic lemmas needed for this project that are currently missing from mathlib.

Here is the list of files that do not depend on any other PersistentDecomp file, indicating they are good candidates for upstreaming to mathlib:

{% include files_to_upstream.md %}

## Acknowledgements

Our project relies on mathlib and we thank all who have contributed on it in some manner for their help.

## Source reference

`[BC]` : https://arxiv.org/pdf/1811.08946

[BC]: https://arxiv.org/pdf/1811.08946
