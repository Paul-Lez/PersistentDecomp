# Decomposition of Persistence Modules

The objective of this repository is to formalise the statement of the barcode decomposition theorem of persistence modules into the Lean proof assistant.

## Source

The main source for our work is the paper "Decomposition of Persistence Modules" authored by Magnus Bakke Botnan and William Crawley-Boevey. This paper is available [here](https://arxiv.org/pdf/1811.08946).

The main result we currently aim to prove is Theorem 1.1: *Any pointwise finite-dimensional persistence module is a direct sum of indecomposable modules with local endomorphism ring*.

## Contents

The code is contained in the directory `PH_formalisation`. It contains the following subdirectories:
* `Mathlib`: contains material missing from current files in Mathlib.
* `Prereqs`: contains basic definitions and properties of persistence modules.

In addition, we also have the following files:
* `DirectSumDecomposition`: defines direct sum decompositions of persistence modules and proves basic facts about them.
* `thm1_1`: proves that indecomposable modules have local endomorphism rings.
* `step_2`: proves that pointwise finite-dimensional persistence modules decompose as a direct sum of indecomposable modules.

## Future Considerations

Once Theorem 1.1 is proven, we hope to be able to prove Theorem 1.2: *Pointwise finite-dimensional persistence modules over a totally ordered set decompose into interval modules*. This result is frequently used in topological data analysis, and hence it should be upstreamed to mathlib.

The current implementation views persistence modules and persistence submodules as purely separate objects. It should be a future goal to unify them.

## Acknowledgements

Our project relies on mathlib and we thank all who have contributed on it in some manner for their help.
