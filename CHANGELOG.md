# NanoYalla: a kernel representation of linear logic in Coq

## version 1.0

* **1.0.0**: **initial version** coming from previous work in the [Yalla library](https://perso.ens-lyon.fr/olivier.laurent/yalla/)
* **1.0.1**: extended backward compatibility *(tested with Coq ≥ 8.8)*
* **1.0.2**: added `ax_expansion` tactic
* **1.0.3**: added utf-8 notations
* **1.0.4**: added axiomatic approach for cut

## version 1.1

* **1.1.0**: **parameterized installation for cut**: with or without Yalla *(tested with Coq ≥ 8.10)*
* **1.1.1**: simplified `ax_expansion` tactic
* **1.1.2**: turned `ex_perm_r` into a `Notation` with `nat` scope
* **1.1.3**: added `cbn_sequent` tactic for controled unfolding
* **1.1.4**: added `Set Implicit Arguments` and used BNF-style definition of `formula` *(tested with Coq ≥ 8.12)*

