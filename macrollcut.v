From NanoYalla Require Export nanollcut.

Lemma cut_r_ext l1 A l2 : ll (l1 ++ A :: nil) -> ll (dual A :: l2) -> ll (l1 ++ l2).
Proof.
intros pi1%(ex_transp_middle2 nil) pi2.
replace (l1 ++ nil) with l1 in pi1; [ | induction l1; intuition ].
apply (cut_r A); assumption.
Defined.
