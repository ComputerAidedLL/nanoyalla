From Coq Require Import List PeanoNat Compare_dec.
From NanoYalla Require Export nanoll.

Export List.ListNotations.

Set Implicit Arguments.


(** * Informative / Transparent versions of list operations *)

Lemma app_assoc_inf A (l m n : list A) : l ++ m ++ n = (l ++ m) ++ n.
Proof. induction l; cbn; f_equal. assumption. Defined.

Lemma map_length_inf A B (f : A -> B) l : length (map f l) = length l.
Proof. induction l as [|a l IHl]; cbn; [ | rewrite IHl ]; reflexivity. Defined.


(** * Permutations *)

(* Transpose elements of index n and S n in l *)
Fixpoint transpS A n (l : list A) :=
  match n, l with
  | 0, x :: y :: r => y :: x :: r
  | S n, x :: r => x :: transpS n r
  | _, r => r
  end.

(* Transpose elements of index n and S (n + m) in l *)
Fixpoint transp A n m (l : list A) :=
  match m with
  | 0 => transpS n l
  | S m => transpS n (transp (S n) m (transpS n l))
  end.

(* Apply list of transpositions described as a [list (option nat)]:
   [Some k0; ...; Some kn] means (n, n + S kn) o ... o (0, S k0)
   and None is "no permutation at this position" *)
Fixpoint transpL A s (l : list A) :=
  match s with
  | Some k :: s => match transp 0 k l with
                   | x :: r => x :: transpL s r
                   | nil => l
                   end
  | None :: s => match l with
                 | x :: r => x :: transpL s r
                 | nil => l
                 end
  | nil => l
  end.

(* Map a permutation of n elements
   described as a [list nat] of distinct elements between 0 and n-1
   into a list of transpositions as used by [transpL] *)
Definition permL_of_perm : list nat -> list (option nat).
Proof.
intros p.
remember (length p) as n eqn:Heqn.
induction n as [|n IHn] in p, Heqn |- *.
- exact nil.
- destruct p as [|[|x] p]; inversion Heqn as [Hn].
  + rewrite <- (map_length_inf pred) in Hn.
    exact (None :: IHn _ Hn).
  + rewrite <- (map_length_inf (fun k => if Nat.eqb k 0 then x else pred k) p) in Hn.
    exact (Some x :: IHn _ Hn).
Defined.

(* Properties *)

Lemma transpS_lt A n (l : list A) : S n < length l ->
 {'(l1, l2, a, b) | (l = l1 ++ a :: b :: l2 /\ length l1 = n) & transpS n l = l1 ++ b :: a :: l2}.
Proof.
induction n as [|n IHn] in l |- *; cbn; intros Hl.
- destruct l as [|a [|b l]]; cbn in Hl; [ exfalso; inversion Hl | exfalso; exact (Nat.lt_irrefl _ Hl) | ].
  exists (nil, l, a, b); repeat split.
- destruct l as [|a l]; cbn in Hl; [ exfalso; inversion Hl | ].
  destruct (IHn l) as [[[[l1 l2] b] c] [-> Hl1] ->]; [ exact (proj2 (Nat.succ_lt_mono _ _) Hl) | ].
  exists (a :: l1, l2, b, c); split; cbn; [ | subst n ]; reflexivity.
Defined.

Lemma transpS_overflow A n (l : list A) : length l <= S n -> transpS n l = l.
Proof.
induction n as [|n IHn] in l |- *; cbn; intros Hl.
- destruct l as [|a [|b l]]; [ reflexivity | reflexivity | ].
  exfalso. inversion Hl as [|k Hl']. inversion Hl'.
- destruct l as [|a l]; [ reflexivity | ].
  cbn in Hl. apply <- Nat.succ_le_mono in Hl.
  f_equal. exact (IHn l Hl).
Defined.

Lemma transpS_compute A l1 (a b : A) l2 :
  transpS (length l1) (l1 ++ a :: b :: l2) = l1 ++ b :: a :: l2.
Proof.
destruct (@transpS_lt _ (length l1) (l1 ++ a :: b :: l2)) as [[[[l1' l2'] c] d] [Heq Hl] ->].
- induction l1; apply -> Nat.succ_lt_mono; [ apply Nat.lt_0_succ | ]. assumption.
- induction l1 as [|h l1 IHl1] in l1', Heq, Hl |- *; cbn; destruct l1' as [|a' l1']; inversion Heq;
    [ reflexivity | discriminate Hl | discriminate Hl | subst ].
  injection Hl as [=].
  cbn. f_equal. apply IHl1; assumption.
Defined.

Lemma transp_cons A a b x (l : list A) :
  transp (S a) b (x :: l) = x :: transp a b l.
Proof. induction b as [|b IHb] in a, l |- *; [ | cbn; rewrite (IHb (S a)) ]; reflexivity. Defined.

Lemma transp_app_tl A l0 a b (l : list A) :
  transp (length l0 + a) b (l0 ++ l) = l0 ++ transp a b l.
Proof. induction l0 as [|x l0 IHl0] in a, l |- *; [| cbn; rewrite transp_cons, <- IHl0 ]; reflexivity. Defined.

(* Extended exchange rules *)

Lemma ex_transpS n l : ll l -> ll (transpS n l).
Proof.
intros pi.
destruct (le_lt_dec (length l) (S n)) as [Hle|Hlt].
- rewrite transpS_overflow; assumption.
- apply transpS_lt in Hlt as [[[[l1 l2] b] c] [-> _] ->].
  apply ex_t_r, pi.
Defined.

Lemma ex_transp n m l : ll l -> ll (transp n m l).
Proof.
induction m as [|m IHm] in n, l |- *; intros pi.
- apply ex_transpS, pi.
- apply ex_transpS, IHm, ex_transpS, pi.
Defined.

Lemma ex_transp_middle1 l1 l2 l3 A : ll (l1 ++ A :: l2 ++ l3) -> ll (l1 ++ l2 ++ A :: l3).
Proof.
induction l2 as [|a l2 IHl2] in l1 |- *; cbn; intros pi; [ exact pi | ].
replace (l1 ++ a :: l2 ++ A :: l3)
   with ((l1 ++ a :: nil) ++ l2 ++ A :: l3)
  by (rewrite <- app_assoc_inf; reflexivity).
apply IHl2. rewrite <- app_assoc_inf. cbn.
rewrite <- transpS_compute.
apply (ex_transpS (length l1)), pi.
Defined.

Lemma ex_transp_middle2 l1 l2 l3 A : ll (l1 ++ l2 ++ A :: l3) -> ll (l1 ++ A :: l2 ++ l3).
Proof.
induction l2 as [|a l2 IHl2] in l1 |- *; cbn; intros pi; [ exact pi | ].
replace (l1 ++ a :: l2 ++ A :: l3)
   with ((l1 ++ a :: nil) ++ l2 ++ A :: l3) in pi
  by (rewrite <- app_assoc_inf; reflexivity).
apply IHl2 in pi. rewrite <- app_assoc_inf in pi. cbn in pi.
rewrite <- transpS_compute.
apply (ex_transpS (length l1)), pi.
Defined.

Lemma ex_transpL s l : ll l -> ll (transpL s l).
Proof.
enough (forall l0, ll (l0 ++ l) -> ll (l0 ++ transpL s l)) as Hs
  by (intros pi; apply (Hs nil), pi).
induction s as [|[n|] s IHs] in l |- *; cbn; intros l0 pi; [ exact pi | | ].
- remember (transp 0 n l) as lt eqn:Heqlt.
  destruct lt as [|f lt]; [ exact pi | ].
  replace (l0 ++ f :: transpL s lt) with ((l0 ++ f :: nil) ++ transpL s lt)
    by (rewrite <- app_assoc_inf; reflexivity).
  apply IHs.
  rewrite <- app_assoc_inf. cbn.
  rewrite Heqlt, <- transp_app_tl.
  apply ex_transp, pi.
- destruct l as [|f l]; [ exact pi | ].
  replace (l0 ++ f :: transpL s l) with ((l0 ++ f :: nil) ++ transpL s l)
    by (rewrite <- app_assoc_inf; reflexivity).
  apply IHs.
  rewrite <- app_assoc_inf. exact pi.
Defined.


(** * Extended rules *)

Fixpoint dual A :=
match A with
| var x     => covar x
| covar x   => var x
| one       => bot
| bot       => one
| tens A B  => parr (dual A) (dual B)
| parr A B  => tens (dual A) (dual B)
| zero      => top
| top       => zero
| aplus A B => awith (dual A) (dual B)
| awith A B => aplus (dual A) (dual B)
| oc A      => wn (dual A)
| wn A      => oc (dual A)
end.

Lemma bidual A : dual (dual A) = A.
Proof.
induction A as [ X | X
               | | | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2
               | | | A1 IHA1 A2 IHA2 | A1 IHA1 A2 IHA2
               | A1 IHA1 | A1 IHA1 ];
cbn; rewrite ?IHA1, ?IHA2; reflexivity.
Defined.

Notation ex_perm_r p := (ex_transpL (permL_of_perm (p%nat))).

Lemma ax_r_ext A : ll (dual A :: A :: nil).
Proof.
induction A as [ X | X
               | | | A1 IHA1 A2 IHA2|A1 IHA1 A2 IHA2
               | | | A1 IHA1 A2 IHA2|A1 IHA1 A2 IHA2
               | A1 IHA1 | A1 IHA1 ]; cbn.
- apply ax_r.
- apply (ex_t_r nil), ax_r.
- apply bot_r, one_r.
- apply (ex_t_r nil), bot_r, one_r.
- apply parr_r.
  apply (ex_t_r (dual A1 :: nil)), (ex_t_r nil).
  change (ll (tens A1 A2 :: (dual A1 :: nil) ++ dual A2 :: nil)).
  apply tens_r; apply (ex_t_r nil); assumption.
- apply (ex_t_r nil).
  apply parr_r.
  apply (ex_t_r (A1 :: nil)), (ex_t_r nil).
  change (ll (tens (dual A1) (dual A2) :: (A1 :: nil) ++ A2 :: nil)).
  apply tens_r; assumption.
- apply top_r.
- apply (ex_t_r nil), top_r.
- apply with_r; apply (ex_t_r nil).
  + apply plus_r1, (ex_t_r nil), IHA1.
  + apply plus_r2, (ex_t_r nil), IHA2.
- apply (ex_t_r nil), with_r; apply (ex_t_r nil).
  + apply plus_r1, IHA1.
  + apply plus_r2, IHA2.
- apply (ex_t_r nil).
  change (ll (oc A1 :: map wn (dual A1 :: nil))).
  apply oc_r. cbn.
  apply (ex_t_r nil).
  apply de_r, IHA1.
- change (ll (oc (dual A1) :: map wn (A1 :: nil))).
  apply oc_r. cbn.
  apply (ex_t_r nil), de_r, (ex_t_r nil), IHA1.
Defined.

Ltac ax_expansion :=
  now cbn;
  let Hax := fresh "Hax" in
  match goal with
  | |- ll (?A :: ?B :: nil) => assert (Hax := ax_r_ext B); cbn in Hax; rewrite ?bidual in Hax
  end.

Definition one_r_ext := one_r.

Lemma bot_r_ext l1 l2 : ll (l1 ++ l2) -> ll (l1 ++ bot :: l2).
Proof. intro pi. apply (ex_transp_middle1 nil), bot_r, pi. Defined.

Lemma top_r_ext l1 l2 : ll (l1 ++ top :: l2).
Proof. apply (ex_transp_middle1 nil), top_r. Defined.

Lemma tens_r_ext l1 A B l2 : ll (l1 ++ A :: nil) -> ll (B :: l2) -> ll (l1 ++ tens A B :: l2).
Proof.
intros pi1 pi2.
apply (ex_transp_middle1 nil). cbn.
apply tens_r, pi2.
apply (ex_transp_middle2 nil) in pi1.
replace (l1 ++ nil) with l1 in pi1; [ exact pi1 | ].
clear. induction l1; [ reflexivity | ]. cbn. f_equal. assumption.
Defined.

Lemma parr_r_ext l1 A B l2 : ll (l1 ++ A :: B :: l2) -> ll (l1 ++ parr A B :: l2).
Proof.
intro pi.
apply (ex_transp_middle1 nil), parr_r.
apply (ex_transp_middle2 (A :: nil)). cbn. apply (ex_transp_middle2 nil), pi.
Defined.

Lemma with_r_ext l1 A B l2 : ll (l1 ++ A :: l2) -> ll (l1 ++ B :: l2) -> ll (l1 ++ awith A B :: l2).
Proof. intros. apply (ex_transp_middle1 nil), with_r; apply (ex_transp_middle2 nil); assumption. Defined.

Lemma plus_r1_ext l1 A B l2 : ll (l1 ++ A :: l2) -> ll (l1 ++ aplus A B :: l2).
Proof. intro pi. apply (ex_transp_middle1 nil), plus_r1, (ex_transp_middle2 nil), pi. Defined.

Lemma plus_r2_ext l1 A B l2 : ll (l1 ++ A :: l2) -> ll (l1 ++ aplus B A :: l2).
Proof. intro pi. apply (ex_transp_middle1 nil), plus_r2, (ex_transp_middle2 nil), pi. Defined.

Lemma oc_r_ext l1 A l2 : ll (map wn l1 ++ A :: map wn l2) -> ll (map wn l1 ++ oc A :: map wn l2).
Proof.
intros pi%(ex_transp_middle2 nil).
apply (ex_transp_middle1 nil). cbn.
replace (map wn l1 ++ map wn l2) with (map wn (l1 ++ l2)) in *; [ apply oc_r, pi | ].
clear. induction l1; [ reflexivity | ]. cbn. f_equal. assumption.
Defined.

Lemma de_r_ext l1 A l2 : ll (l1 ++ A :: l2) -> ll (l1 ++ wn A :: l2).
Proof. intro pi. apply (ex_transp_middle1 nil), de_r, (ex_transp_middle2 nil), pi. Defined.

Lemma wk_r_ext l1 A l2 : ll (l1 ++ l2) -> ll (l1 ++ wn A :: l2).
Proof. intro pi. apply (ex_transp_middle1 nil), wk_r, pi. Defined.

Lemma co_r_ext l1 A l2 : ll (l1 ++ wn A :: wn A :: l2) -> ll (l1 ++ wn A :: l2).
Proof.
intro pi. apply (ex_transp_middle1 nil), co_r, (ex_transp_middle2 (wn A :: nil)), (ex_transp_middle2 nil l1), pi.
Defined.

Ltac cbn_sequent := cbn beta iota delta[app map dual]; rewrite ?bidual.

Declare Scope ll_scope.
Bind Scope ll_scope with formula.
Open Scope ll_scope.

Module LLNotations.
  Notation "⊢" := (ll nil) (format "⊢") : ll_scope.
  Notation "⊢ x" := (ll (cons x nil)) (at level 85) : ll_scope.
  Notation "⊢ x , y , .. , z" := (ll (cons x (cons y .. (cons z nil) ..))) (at level 85) : ll_scope.
  Infix "⊗" := tens (at level 40) : ll_scope.
  Infix "⊕" := aplus (at level 40) : ll_scope.
  Infix "⅋" := parr (at level 40) : ll_scope.
  Infix "＆" := awith (at level 40) : ll_scope.
  Notation "? A" := (wn A) (format "? A", at level 31, right associativity) : ll_scope.
  Notation "! A" := (oc A) (format "! A", at level 31, right associativity) : ll_scope.
  Notation "1" := one : ll_scope.
  Notation "⟂" := bot : ll_scope.
  Notation "0" := zero : ll_scope.
  Notation "⊤" := top : ll_scope.
  Notation "A ^" := (dual A) (at level 12, format "A ^") : ll_scope.
End LLNotations.
