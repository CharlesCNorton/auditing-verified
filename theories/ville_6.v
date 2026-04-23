(******************************************************************************)
(*                                                                            *)
(*     Discrete supermartingale theory and Ville's inequality                 *)
(*                                                                            *)
(*     Defines filtrations, conditional expectation, supermartingales,        *)
(*     and proves:                                                            *)
(*       - Tower property: E[E[X|F_n]] = E[X]                               *)
(*       - Ville's inequality: Pr(M_n >= 1/alpha) <= alpha                   *)
(*       - Optional stopping theorem for bounded stopping times              *)
(*       - Doob's maximal inequality                                          *)
(*       - Filtration-partition equivalence                                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp.reals Require Import reals.

From Auditing Require Import auditing_1 probability_4.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Open Scope ring_scope.

(** ** Core definitions and tower property *)

Section DiscreteVille.

Variable R : realType.
Variable Omega : finType.
Variable mu : Omega -> R.
Hypothesis mu_ge0 : forall x : Omega, 0 <= mu x.
Hypothesis mu_sum1 : \sum_x mu x = 1.

(** [filtration F]: [F] is a discrete filtration -- a sequence of equivalence
    relations that refine over time. *)
Definition filtration (F : nat -> Omega -> Omega -> bool) :=
  [/\ (forall n, reflexive (F n)) ,
      (forall n, symmetric (F n)) ,
      (forall n, transitive (F n)) &
      (forall n x y, F n.+1 x y -> F n x y) ].

(** [filtration_pos F]: a filtration with positive cell mass -- bundles
    the cell-positivity hypothesis [Hcell] that many consumers need. *)
Definition filtration_pos (F : nat -> Omega -> Omega -> bool) :=
  filtration F /\ (forall k x, 0 < \sum_(y | F k x y) mu y).

(** Extract the filtration from a [filtration_pos]. *)
Lemma filtration_pos_filt (F : nat -> Omega -> Omega -> bool) :
  filtration_pos F -> filtration F.
Proof. by case. Qed.

(** Extract the cell-positivity from a [filtration_pos]. *)
Lemma filtration_pos_cell (F : nat -> Omega -> Omega -> bool) :
  filtration_pos F -> forall k x, 0 < \sum_(y | F k x y) mu y.
Proof. by case. Qed.

(** [cond_exp F X n x]: conditional expectation of [X] given the partition
    cell of [F n] containing [x]. *)
Definition cond_exp (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (n : nat) (x : Omega) : R :=
  (\sum_(y | F n x y) mu y * X y) / \sum_(y | F n x y) mu y.

(** [adapted F X]: the process [X] is adapted to filtration [F], i.e.,
    [X n] is measurable with respect to [F n]. *)
Definition adapted (F : nat -> Omega -> Omega -> bool)
    (X : nat -> Omega -> R) :=
  forall n x y, F n x y -> X n x = X n y.

(** [supermartingale F X]: [X] is an [F]-adapted process whose conditional
    expectation at each step is at most the current value. *)
Definition supermartingale (F : nat -> Omega -> Omega -> bool)
    (X : nat -> Omega -> R) :=
  adapted F X /\
  forall n x, cond_exp F (X n.+1) n x <= X n x.

(** [martingale F X]: [X] is an [F]-adapted process whose conditional
    expectation at each step equals the current value. *)
Definition martingale (F : nat -> Omega -> Omega -> bool)
    (X : nat -> Omega -> R) :=
  adapted F X /\
  forall n x, cond_exp F (X n.+1) n x = X n x.

(** [submartingale F X]: [X] is an [F]-adapted process whose conditional
    expectation at each step is at least the current value. *)
Definition submartingale (F : nat -> Omega -> Omega -> bool)
    (X : nat -> Omega -> R) :=
  adapted F X /\
  forall n x, X n x <= cond_exp F (X n.+1) n x.

(** Every martingale is a supermartingale (equality implies <=). *)
Lemma martingale_is_supermartingale (F : nat -> Omega -> Omega -> bool)
    (X : nat -> Omega -> R) :
  martingale F X -> supermartingale F X.
Proof. by move=> [Hadapt Hmart]; split => // n x; rewrite Hmart. Qed.

(** Every martingale is a submartingale (equality implies >=). *)
Lemma martingale_is_submartingale (F : nat -> Omega -> Omega -> bool)
    (X : nat -> Omega -> R) :
  martingale F X -> submartingale F X.
Proof. by move=> [Hadapt Hmart]; split => // n x; rewrite Hmart. Qed.

(** [stopping_time F tau]: [tau] is a stopping time with respect to [F],
    meaning the event [{tau <= n}] is [F n]-measurable. *)
Definition stopping_time (F : nat -> Omega -> Omega -> bool)
    (tau : Omega -> nat) :=
  forall n x y, F n x y -> (tau x <= n)%N = (tau y <= n)%N.

(** Conditional expectation of an [F n]-measurable function is the function itself. *)
Lemma cond_exp_measurable (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (n : nat) (x : Omega) :
  filtration F ->
  (forall y, F n x y -> X y = X x) ->
  0 < \sum_(y | F n x y) mu y ->
  cond_exp F X n x = X x.
Proof.
move=> [Hrefl _ _ _] Hmeas Hpos.
rewrite /cond_exp.
have -> : \sum_(y | F n x y) mu y * X y =
          X x * \sum_(y | F n x y) mu y.
  by rewrite mulr_sumr; apply: eq_bigr => y Hy; rewrite Hmeas // mulrC.
by rewrite mulfK ?gt_eqF.
Qed.

(** Conditional expectation is idempotent: [E[E[X|F_n] | F_n] = E[X|F_n]]. *)
Lemma cond_exp_idempotent (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (n : nat) (x : Omega) :
  filtration F ->
  0 < \sum_(y | F n x y) mu y ->
  cond_exp F (cond_exp F X n) n x = cond_exp F X n x.
Proof.
move=> HF Hcell; apply: cond_exp_measurable => // y Hxy.
have [_ Hsym Htrans _] := HF.
have Hbigl : F n y =1 F n x.
  move=> z; apply/idP/idP.
  - by move=> Hyz; apply: (Htrans n y _ _ Hxy Hyz).
  - by move=> Hxz; apply: (Htrans n x); [rewrite (Hsym n) |].
by rewrite /cond_exp; congr (_ / _); apply: eq_bigl.
Qed.

(** Filtration monotonicity: if [m <= n] and [F n x y], then [F m x y]. *)
Lemma filtration_mono (F : nat -> Omega -> Omega -> bool)
    (m n : nat) (x y : Omega) :
  filtration F -> (m <= n)%N -> F n x y -> F m x y.
Proof.
move=> [_ _ _ Href]; elim: n => [|n IH].
  by rewrite leqn0 => /eqP ->.
rewrite leq_eqVlt => /orP [/eqP -> //|].
by rewrite ltnS => Hmn Hn1; exact: IH Hmn (Href n x y Hn1).
Qed.

(** If [x] and [y] are in the same [F n] cell and both have stopped by time
    [n], then they stopped at the same time. *)
Lemma stopping_time_cell_eq (F : nat -> Omega -> Omega -> bool)
    (tau : Omega -> nat) (n : nat) (x y : Omega) :
  filtration F -> stopping_time F tau ->
  F n x y -> (tau x <= n)%N -> (tau y <= n)%N ->
  tau x = tau y.
Proof.
move=> HF Hstop Hxy Htx Hty; apply/eqP; rewrite eqn_leq; apply/andP; split.
- by have := Hstop (tau y) x y (filtration_mono HF Hty Hxy); rewrite leqnn => ->.
- by have := Hstop (tau x) x y (filtration_mono HF Htx Hxy); rewrite leqnn => <-.
Qed.

(** Conditional expectation is extensional: functions agreeing on the cell
    have the same conditional expectation. *)
Lemma cond_exp_ext (F : nat -> Omega -> Omega -> bool)
    (X Y : Omega -> R) (n : nat) (x : Omega) :
  (forall y, F n x y -> X y = Y y) ->
  cond_exp F X n x = cond_exp F Y n x.
Proof.
move=> Heq; rewrite /cond_exp; congr (_ / _).
by apply: eq_bigr => y Hy; rewrite (Heq _ Hy).
Qed.

(** [Exp X]: expectation of [X] under the probability measure [mu]. *)
Definition Exp (X : Omega -> R) : R :=
  \sum_(x : Omega) mu x * X x.

(** Expectation can be written as a sum restricted to the trivial predicate. *)
Lemma Exp_sum_predT (X : Omega -> R) :
  Exp X = \sum_(x : Omega | predT x) mu x * X x.
Proof. by rewrite /Exp big_mkcond /=. Qed.

(** The probability of any event is at most 1. *)
Lemma Pr_le1_ville (P : pred Omega) : @Pr R _ mu P <= 1.
Proof.
rewrite -mu_sum1 /Pr big_mkcond /=.
elim/big_ind2: _ => [//|a1 a2 b1 b2 Ha Hb|x] //.
- exact: lerD.
- by case: (P x) => //; exact: mu_ge0.
Qed.

(** Probability of an event equals the expectation of its indicator function. *)
Lemma Pr_Exp (P : pred Omega) :
  @Pr R _ mu P = Exp (fun x => if P x then 1 else 0).
Proof.
rewrite /Pr /Exp big_mkcond /=.
by apply: eq_bigr => x _; case: (P x); rewrite ?mulr1 ?mulr0.
Qed.

(** A partial sum over a non-negative integrand is at most the full expectation. *)
Lemma Exp_ge_partial (X : Omega -> R) (P : pred Omega) :
  (forall x, 0 <= mu x * X x) ->
  \sum_(x | P x) mu x * X x <= Exp X.
Proof.
move=> Hge0; rewrite /Exp big_mkcond.
elim/big_ind2: _ => [|a1 a2 b1 b2 Ha Hb|x] //.
- exact: lerD.
- by case: (P x) => //; exact: Hge0.
Qed.

(** Markov's inequality: [c * Pr(X >= c) <= E[X]] for non-negative [X] and [c > 0]. *)
Lemma markov_ineq (X : Omega -> R) (c : R) :
  0 < c ->
  (forall x, 0 <= X x) ->
  c * @Pr R _ mu (fun x => c <= X x) <= Exp X.
Proof.
move=> Hc HX; rewrite /Pr mulr_sumr.
apply: (le_trans (y := \sum_(x | c <= X x) mu x * X x)).
  apply: ler_sum => x Hle.
  by rewrite mulrC; apply: ler_wpM2l; [exact: mu_ge0 |].
apply: Exp_ge_partial => x.
by apply: mulr_ge0; [exact: mu_ge0 | exact: HX].
Qed.

(** Equivalent elements have the same cell mass: if [F_eq x y] then
    the sum of [mu] over the cell of [x] equals the sum over the cell of [y]. *)
Lemma equiv_class_sum (F_eq : Omega -> Omega -> bool) (x y : Omega) :
  transitive F_eq -> symmetric F_eq ->
  F_eq x y ->
  \sum_(z | F_eq x z) mu z = \sum_(z | F_eq y z) mu z.
Proof.
move=> Htrans Hsym Hxy; apply: eq_bigl => z; apply/idP/idP.
- by move=> Hxz; apply: (Htrans x); [rewrite Hsym |].
- by exact: (Htrans y).
Qed.

(** Tower property at a single level: [E[E[X | F n]] = E[X]].  The
    equivalence-relation structure at [n] alone suffices; the
    refinement axiom of a forward filtration is not needed, so this
    form applies to forward and reverse filtrations alike.

    Proof sketch:
    1. Rewrite the LHS as a double sum over (x, y) pairs where
       [F n x y], weighting each term by [mu x / cell_mass(x)].
    2. Flatten to a sum over pairs via [pair_big_dep].
    3. For the RHS, factor [mu y * X y] out of each inner sum and
       show the remaining cell-mass ratios sum to 1 via
       [equiv_class_sum] (equivalent elements have equal cell mass).
    4. Flatten the RHS the same way, then apply [reindex_inj] with
       the pair-swap bijection [(x,y) -> (y,x)] to match the two
       flattened sums. *)
Lemma tower_property_level (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (n : nat) :
  (forall k, reflexive (F k)) ->
  (forall k, symmetric (F k)) ->
  (forall k, transitive (F k)) ->
  (forall x, 0 < \sum_(y | F n x y) mu y) ->
  Exp (cond_exp F X n) = Exp X.
Proof.
move=> Hrefl Hsym Htrans Hcell.
rewrite /Exp /cond_exp.
have Hpred : forall (G : Omega -> R),
  \sum_(x : Omega) G x = \sum_(x | predT x) G x
  by move=> G; rewrite big_mkcond /=.
rewrite !Hpred.
have Hbody : forall x,
  mu x * ((\sum_(y | F n x y) mu y * X y) / \sum_(y | F n x y) mu y) =
  \sum_(y | F n x y) mu y * X y * (mu x / \sum_(z | F n x z) mu z).
  move=> x; rewrite /cond_exp.
  transitivity ((\sum_(y | F n x y) mu y * X y) *
    (mu x / \sum_(y | F n x y) mu y)); first by rewrite mulrCA.
  by rewrite mulr_suml.
transitivity (\sum_(x | predT x) \sum_(y | F n x y)
  mu y * X y * (mu x / \sum_(z | F n x z) mu z)).
  by apply: eq_bigr => x _; exact: Hbody.
have Hinj : injective (fun p : Omega * Omega => (p.2, p.1))
  by move=> [a b] [c d] /= [-> ->].
rewrite (pair_big_dep predT (F n)) /=.
symmetry.
transitivity (\sum_(y | predT y) \sum_(x | F n x y)
  mu y * X y * (mu x / \sum_(z | F n x z) mu z)).
  apply: eq_bigr => y _; rewrite -[LHS]mulr1 -mulr_sumr; congr (_ * _).
  under eq_bigr => x Hxy do
    rewrite (equiv_class_sum (F_eq := F n) (Htrans n) (Hsym n) Hxy).
  rewrite -mulr_suml.
  have -> : \sum_(j | F n j y) mu j = \sum_(z | F n y z) mu z
    by apply: eq_bigl => z; rewrite (Hsym n).
  by rewrite divff // gt_eqF.
rewrite (pair_big_dep predT (fun y x => F n x y)) /=.
by rewrite (reindex_inj Hinj) /=.
Qed.

(** Tower property for a forward filtration.  Discharges [filtration F]
    to extract reflexivity, symmetry, and transitivity at level [n],
    then applies [tower_property_level]. *)
Lemma tower_property (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (n : nat) :
  filtration F ->
  (forall x, 0 < \sum_(y | F n x y) mu y) ->
  Exp (cond_exp F X n) = Exp X.
Proof. by move=> [Hrefl Hsym Htrans _]; exact: tower_property_level. Qed.

(** ** Linearity of conditional expectation and combined (super)martingales *)

(** Conditional expectation scales through a constant factor. *)
Lemma cond_exp_scalar_mul (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (c : R) (n : nat) (x : Omega) :
  cond_exp F (fun y => c * X y) n x = c * cond_exp F X n x.
Proof.
rewrite /cond_exp.
rewrite (eq_bigr (fun y => c * (mu y * X y))); last first.
  by move=> y _; rewrite mulrCA.
by rewrite -mulr_sumr -mulrA.
Qed.

(** Conditional expectation distributes over pointwise addition. *)
Lemma cond_exp_add (F : nat -> Omega -> Omega -> bool)
    (X Y : Omega -> R) (n : nat) (x : Omega) :
  cond_exp F (fun y => X y + Y y) n x =
    cond_exp F X n x + cond_exp F Y n x.
Proof.
rewrite /cond_exp -mulrDl; congr (_ / _).
rewrite -big_split /=.
by apply: eq_bigr => y _; rewrite mulrDr.
Qed.

(** Non-negative scalar multiplication preserves the supermartingale property. *)
Lemma supermartingale_scalar_mul (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (c : R) :
  0 <= c -> supermartingale F M ->
  supermartingale F (fun n x => c * M n x).
Proof.
move=> Hc [Hadapt Hsup]; split.
- by move=> n x y Hxy; rewrite (Hadapt n x y Hxy).
- move=> n x; rewrite cond_exp_scalar_mul.
  exact: ler_wpM2l.
Qed.

(** Pointwise addition preserves the supermartingale property. *)
Lemma supermartingale_sum (F : nat -> Omega -> Omega -> bool)
    (M1 M2 : nat -> Omega -> R) :
  supermartingale F M1 -> supermartingale F M2 ->
  supermartingale F (fun n x => M1 n x + M2 n x).
Proof.
move=> [H1a H1s] [H2a H2s]; split.
- by move=> n x y Hxy; rewrite (H1a n x y Hxy) (H2a n x y Hxy).
- by move=> n x; rewrite cond_exp_add; apply: lerD; [exact: H1s | exact: H2s].
Qed.

(** Scalar multiplication preserves the martingale property (any [c]). *)
Lemma martingale_scalar_mul (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (c : R) :
  martingale F M ->
  martingale F (fun n x => c * M n x).
Proof.
move=> [Hadapt Hmart]; split.
- by move=> n x y Hxy; rewrite (Hadapt n x y Hxy).
- by move=> n x; rewrite cond_exp_scalar_mul Hmart.
Qed.

(** Pointwise addition preserves the martingale property. *)
Lemma martingale_sum (F : nat -> Omega -> Omega -> bool)
    (M1 M2 : nat -> Omega -> R) :
  martingale F M1 -> martingale F M2 ->
  martingale F (fun n x => M1 n x + M2 n x).
Proof.
move=> [H1a H1m] [H2a H2m]; split.
- by move=> n x y Hxy; rewrite (H1a n x y Hxy) (H2a n x y Hxy).
- by move=> n x; rewrite cond_exp_add H1m H2m.
Qed.

(** A supermartingale has non-increasing expected value at each step. *)
Lemma supermartingale_Exp_mono (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  filtration F ->
  supermartingale F M ->
  (forall x, 0 < \sum_(y | F n x y) mu y) ->
  Exp (M n.+1) <= Exp (M n).
Proof.
move=> HF [Hadapt Hsup] Hcell.
apply: (le_trans (y := Exp (cond_exp F (M n.+1) n))).
  by rewrite tower_property.
rewrite /Exp; apply: ler_sum => x _.
by apply: ler_wpM2l; [exact: mu_ge0 | exact: Hsup].
Qed.

(** A supermartingale's expected value at any time [n] is bounded by its
    initial expected value. *)
Lemma supermartingale_Exp_le0 (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  filtration F ->
  supermartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  Exp (M n) <= Exp (M 0).
Proof.
move=> HF Hsup Hcell; elim: n => [|n IH]; first exact: lexx.
apply: (le_trans _ IH).
exact: (@supermartingale_Exp_mono F M n HF Hsup (Hcell n)).
Qed.

(** Ville's inequality: for a non-negative supermartingale with
    [E[M_0] <= 1], the probability that [M_n] exceeds [1/alpha]
    is at most [alpha]. *)
Lemma ville_ineq (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (alpha : R) (n : nat) :
  filtration F ->
  supermartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall k x, 0 <= M k x) ->
  0 < alpha -> alpha < 1 ->
  Exp (M 0) <= 1 ->
  @Pr R _ mu (fun x => alpha^-1 <= M n x) <= alpha.
Proof.
move=> HF Hsup Hcell Hge0 Ha0 Ha1 HExp0.
have Hai : 0 < alpha^-1 by rewrite invr_gt0.
have Hmarkov := @markov_ineq (M n) _ Hai (Hge0 n).
have HExp_n := @supermartingale_Exp_le0 F M n HF Hsup Hcell.
have H1 : alpha^-1 * @Pr R _ mu (fun x => alpha^-1 <= M n x) <= 1
  by exact: le_trans Hmarkov (le_trans HExp_n HExp0).
have H2 := ler_wpM2l (ltW Ha0) H1.
by rewrite mulrA mulfV ?unitfE ?gt_eqF // mul1r mulr1 in H2.
Qed.

(** Tighter two-sided bound: [Pr(M n >= 1/alpha)] lies in [[0, 1 - alpha]]
    when [2 * alpha <= 1]. *)
Lemma ville_step_bound (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (alpha : R) (n : nat) :
  filtration F ->
  supermartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall k x, 0 <= M k x) ->
  0 < alpha -> alpha < 1 ->
  2%:R * alpha <= 1 ->
  Exp (M 0) <= 1 ->
  0 <= @Pr R _ mu (fun x => alpha^-1 <= M n x) <= 1 - alpha.
Proof.
move=> HF Hsup Hcell Hge0 Ha0 Ha1 H2a HExp0.
apply/andP; split; first exact: Pr_ge0.
have Hv : @Pr R _ mu (fun x => alpha^-1 <= M n x) <= alpha.
  have Hai : 0 < alpha^-1 by rewrite invr_gt0.
  have Hm := @markov_ineq (M n) _ Hai (Hge0 n).
  have He := @supermartingale_Exp_le0 F M n HF Hsup Hcell.
  have H1 : alpha^-1 * @Pr R _ mu (fun x => alpha^-1 <= M n x) <= 1
    by exact: le_trans Hm (le_trans He HExp0).
  have H2 := ler_wpM2l (ltW Ha0) H1.
  by rewrite mulrA mulfV ?unitfE ?gt_eqF // mul1r mulr1 in H2.
apply: (le_trans Hv).
by rewrite lerBrDr -mulr2n -mulr_natl.
Qed.

(** Conditional expectation of an indicator-weighted function factors as
    the indicator times the conditional expectation. *)
Lemma cond_exp_indicator (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (A : pred Omega) (n : nat) (x : Omega) :
  filtration F ->
  (forall y, F n x y -> A y = A x) ->
  0 < \sum_(y | F n x y) mu y ->
  cond_exp F (fun z => if A z then X z else 0) n x =
  if A x then cond_exp F X n x else 0.
Proof.
move=> [Hrefl _ _ _] Hmeas Hpos.
rewrite /cond_exp.
case HAx: (A x).
- congr (_ / _); apply: eq_bigr => y Hy.
  by rewrite Hmeas // HAx.
- have -> : \sum_(y | F n x y) mu y * (if A y then X y else 0) = 0.
    by apply: big1 => y Hy; rewrite Hmeas // HAx mulr0.
  by rewrite mul0r.
Qed.

(** Restricted tower property: the tower identity holds when the sum is
    restricted to an [F n]-measurable event [A]. *)
Lemma restricted_tower (F : nat -> Omega -> Omega -> bool)
    (X : Omega -> R) (A : pred Omega) (n : nat) :
  filtration F ->
  (forall x y, F n x y -> A x = A y) ->
  (forall x, 0 < \sum_(y | F n x y) mu y) ->
  \sum_(x | A x) mu x * cond_exp F X n x =
  \sum_(x | A x) mu x * X x.
Proof.
move=> HF Hmeas Hcell.
have Htower := tower_property (fun z => if A z then X z else 0) HF Hcell.
rewrite /Exp in Htower.
have HceA : forall x, mu x * cond_exp F (fun z => if A z then X z else 0) n x =
  if A x then mu x * cond_exp F X n x else 0.
  move=> x; rewrite (cond_exp_indicator X HF _ (Hcell x)); last first.
    by move=> y Hy; rewrite (Hmeas x y Hy).
  by case: (A x); rewrite ?mulr0.
have HmuA : forall x, mu x * (if A x then X x else 0) =
  if A x then mu x * X x else 0.
  by move=> x; case: (A x); rewrite ?mulr0.
rewrite (eq_bigr _ (fun x _ => HceA x)) in Htower.
rewrite (eq_bigr _ (fun x _ => HmuA x)) in Htower.
by rewrite -!big_mkcond in Htower.
Qed.

(** ** Optional stopping theorem *)

(** [stopped_process M tau n x]: the process [M] stopped at time [tau],
    evaluated at time [min(tau(x), n)]. *)
Definition stopped_process (M : nat -> Omega -> R) (tau : Omega -> nat) :=
  fun n (x : Omega) => M (minn (tau x) n) x.

(** Stopping a supermartingale at a stopping time yields a supermartingale. *)
Lemma stopped_process_supermartingale (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (tau : Omega -> nat) :
  filtration F -> supermartingale F M -> stopping_time F tau ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  supermartingale F (stopped_process M tau).
Proof.
move=> HF [Hadapt Hsup] Hstop Hcell; split.
- move=> n x y Hxy; rewrite /stopped_process /=.
  case: (leqP (tau x) n) => Htx.
  + (* goal: M (tau x) x = M (minn (tau y) n) y *)
    have Hty : (tau y <= n)%N by rewrite -(Hstop n x y Hxy).
    have Heq := stopping_time_cell_eq HF Hstop Hxy Htx Hty.
    rewrite Heq.
    have -> : minn (tau y) n = tau y by apply/minn_idPl.
    by apply: Hadapt; exact: @filtration_mono F (tau y) n x y HF Hty Hxy.
  + (* goal: M n x = M (minn (tau y) n) y *)
    have Hty : (n < tau y)%N.
      by rewrite ltnNge -(Hstop n x y Hxy) -ltnNge.
    have -> : minn (tau y) n = n by apply/minn_idPr; exact: ltnW.
    by apply: Hadapt.
- move=> n x; rewrite /stopped_process /=.
  case: (leqP (tau x) n) => Htx.
  + (* goal: cond_exp F (fun y => M (minn (tau y) n.+1) y) n x <= M (tau x) x *)
    have Hext : forall y, F n x y ->
      M (minn (tau y) n.+1) y = M (tau x) y.
      move=> y Hxy.
      have Hty : (tau y <= n)%N by rewrite -(Hstop n x y Hxy).
      have Heq := stopping_time_cell_eq HF Hstop Hxy Htx Hty.
      rewrite Heq.
      have -> : minn (tau y) n.+1 = tau y by apply/minn_idPl; exact: leqW.
      done.
    have Hmeas : forall y, F n x y -> M (tau x) y = M (tau x) x.
      by move=> y0 Hxy0; apply/esym/Hadapt;
         exact: @filtration_mono F (tau x) n x y0 HF Htx Hxy0.
    by rewrite (cond_exp_ext Hext) (cond_exp_measurable HF Hmeas (Hcell n x)).
  + (* goal: cond_exp F (fun y => M (minn (tau y) n.+1) y) n x <= M n x *)
    have Hext : forall y, F n x y ->
      M (minn (tau y) n.+1) y = M n.+1 y.
      move=> y Hxy.
      have Hty : (n < tau y)%N.
        by rewrite ltnNge -(Hstop n x y Hxy) -ltnNge.
      have -> : minn (tau y) n.+1 = n.+1 by apply/minn_idPr.
      done.
    by rewrite (cond_exp_ext Hext); exact: Hsup.
Qed.

(** [stopped_value M tau x]: the value of process [M] at the stopping time
    [tau(x)]. *)
Definition stopped_value (M : nat -> Omega -> R) (tau : Omega -> nat) :=
  fun x : Omega => M (tau x) x.

(** Stopping at a constant time [n] recovers [M n]. *)
Lemma stopped_value_const (M : nat -> Omega -> R) (n : nat) :
  stopped_value M (fun _ => n) = M n.
Proof. by apply: boolp.funext. Qed.

(** The stopped value of a non-negative process is non-negative. *)
Lemma stopped_value_bound (M : nat -> Omega -> R)
    (tau : Omega -> nat) (N : nat) :
  (forall k x, 0 <= M k x) ->
  (forall x, (tau x <= N)%N) ->
  (forall x, 0 <= stopped_value M tau x).
Proof. by move=> Hge0 Hbound x; exact: Hge0. Qed.

(** Optional stopping theorem: for a bounded stopping time [tau <= N],
    [E[M_tau] <= E[M_0]]. *)
Lemma optional_stopping (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (tau : Omega -> nat) (N : nat) :
  filtration F -> supermartingale F M -> stopping_time F tau ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall x, (tau x <= N)%N) ->
  Exp (stopped_value M tau) <= Exp (M 0).
Proof.
move=> HF Hsup Hstop Hcell Hbound.
have Hstopmg := stopped_process_supermartingale HF Hsup Hstop Hcell.
have HeqN : stopped_value M tau = stopped_process M tau N.
  apply: boolp.funext => x; rewrite /stopped_value /stopped_process.
  by have -> : minn (tau x) N = tau x by apply/minn_idPl; exact: Hbound.
have Heq0 : stopped_process M tau 0 = M 0.
  by apply: boolp.funext => x; rewrite /stopped_process minn0.
rewrite HeqN -Heq0.
exact: @supermartingale_Exp_le0 F (stopped_process M tau) N HF Hstopmg Hcell.
Qed.

(** ** Martingale optional stopping: equality *)

(** A martingale has constant expectation at each step. *)
Lemma martingale_Exp_step (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  filtration F ->
  martingale F M ->
  (forall x, 0 < \sum_(y | F n x y) mu y) ->
  Exp (M n.+1) = Exp (M n).
Proof.
move=> HF [Hadapt Hmart] Hcell.
rewrite -(tower_property (M n.+1) HF Hcell) /Exp.
by apply: eq_bigr => x _; rewrite Hmart.
Qed.

(** A martingale's expectation is constant at [E[M_0]] for all [n]. *)
Lemma martingale_Exp_const (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  filtration F ->
  martingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  Exp (M n) = Exp (M 0).
Proof.
move=> HF Hmart Hcell; elim: n => [//|n IH].
by rewrite (@martingale_Exp_step F M n HF Hmart (Hcell n)).
Qed.

(** Stopping a martingale at a stopping time yields a martingale.
    Same case analysis on [tau x <= n] as for supermartingales;
    equalities replace inequalities at the one step that uses the
    martingale identity. *)
Lemma stopped_process_martingale (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (tau : Omega -> nat) :
  filtration F -> martingale F M -> stopping_time F tau ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  martingale F (stopped_process M tau).
Proof.
move=> HF [Hadapt Hmart] Hstop Hcell; split.
- move=> n x y Hxy; rewrite /stopped_process /=.
  case: (leqP (tau x) n) => Htx.
  + have Hty : (tau y <= n)%N by rewrite -(Hstop n x y Hxy).
    have Heq := stopping_time_cell_eq HF Hstop Hxy Htx Hty.
    rewrite Heq.
    have -> : minn (tau y) n = tau y by apply/minn_idPl.
    by apply: Hadapt; exact: @filtration_mono F (tau y) n x y HF Hty Hxy.
  + have Hty : (n < tau y)%N.
      by rewrite ltnNge -(Hstop n x y Hxy) -ltnNge.
    have -> : minn (tau y) n = n by apply/minn_idPr; exact: ltnW.
    by apply: Hadapt.
- move=> n x; rewrite /stopped_process /=.
  case: (leqP (tau x) n) => Htx.
  + have Hext : forall y, F n x y ->
      M (minn (tau y) n.+1) y = M (tau x) y.
      move=> y Hxy.
      have Hty : (tau y <= n)%N by rewrite -(Hstop n x y Hxy).
      have Heq := stopping_time_cell_eq HF Hstop Hxy Htx Hty.
      rewrite Heq.
      have -> : minn (tau y) n.+1 = tau y by apply/minn_idPl; exact: leqW.
      done.
    have Hmeas : forall y, F n x y -> M (tau x) y = M (tau x) x.
      by move=> y0 Hxy0; apply/esym/Hadapt;
         exact: @filtration_mono F (tau x) n x y0 HF Htx Hxy0.
    by rewrite (cond_exp_ext Hext) (cond_exp_measurable HF Hmeas (Hcell n x)).
  + have Hext : forall y, F n x y ->
      M (minn (tau y) n.+1) y = M n.+1 y.
      move=> y Hxy.
      have Hty : (n < tau y)%N.
        by rewrite ltnNge -(Hstop n x y Hxy) -ltnNge.
      have -> : minn (tau y) n.+1 = n.+1 by apply/minn_idPr.
      done.
    by rewrite (cond_exp_ext Hext); exact: Hmart.
Qed.

(** Optional stopping for a martingale: [E[M_tau] = E[M_0]] at any
    bounded stopping time.  Equality, not just [<=]. *)
Lemma martingale_optional_stopping_eq (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (tau : Omega -> nat) (N : nat) :
  filtration F -> martingale F M -> stopping_time F tau ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall x, (tau x <= N)%N) ->
  Exp (stopped_value M tau) = Exp (M 0).
Proof.
move=> HF Hmart Hstop Hcell Hbound.
have Hstopmart := stopped_process_martingale HF Hmart Hstop Hcell.
have HeqN : stopped_value M tau = stopped_process M tau N.
  apply: boolp.funext => x; rewrite /stopped_value /stopped_process.
  by have -> : minn (tau x) N = tau x by apply/minn_idPl; exact: Hbound.
have Heq0 : stopped_process M tau 0 = M 0.
  by apply: boolp.funext => x; rewrite /stopped_process minn0.
rewrite HeqN -Heq0.
exact: (@martingale_Exp_const F (stopped_process M tau) N HF Hstopmart Hcell).
Qed.

(** Ville's inequality applied to stopped values: [Pr(M_tau >= 1/alpha) <= alpha]. *)
Lemma ville_stopping (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (alpha : R) (tau : Omega -> nat) (N : nat) :
  filtration F -> supermartingale F M -> stopping_time F tau ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall k x, 0 <= M k x) ->
  (forall x, (tau x <= N)%N) ->
  0 < alpha -> alpha < 1 -> Exp (M 0) <= 1 ->
  @Pr R _ mu (fun x => alpha^-1 <= stopped_value M tau x) <= alpha.
Proof.
move=> HF Hsup Hstop Hcell Hge0 Hbound Ha0 Ha1 HExp0.
have Hai : 0 < alpha^-1 by rewrite invr_gt0.
have Hsv_ge0 : forall x, 0 <= stopped_value M tau x by move=> x; exact: Hge0.
have Hmarkov := @markov_ineq (stopped_value M tau) _ Hai Hsv_ge0.
have Hopt := optional_stopping HF Hsup Hstop Hcell Hbound.
have H1 : alpha^-1 * @Pr R _ mu (fun x => alpha^-1 <= stopped_value M tau x) <= 1
  by exact: le_trans Hmarkov (le_trans Hopt HExp0).
have H2 := ler_wpM2l (ltW Ha0) H1.
by rewrite mulrA mulfV ?unitfE ?gt_eqF // mul1r mulr1 in H2.
Qed.

(** ** Doob's maximal inequality *)

(** Doob's maximal inequality for stopped processes:
    [c * Pr(M_tau >= c) <= E[M_0]]. *)
Lemma doob_maximal (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (c : R) (tau : Omega -> nat) (N : nat) :
  filtration F -> supermartingale F M -> stopping_time F tau ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall k x, 0 <= M k x) ->
  0 < c ->
  (forall x, (tau x <= N)%N) ->
  c * @Pr R _ mu (fun x => c <= stopped_value M tau x) <= Exp (M 0).
Proof.
move=> HF Hsup Hstop Hcell Hge0 Hc Hbound.
have Hsv_ge0 : forall x, 0 <= stopped_value M tau x by move=> x; exact: Hge0.
have Hmarkov := @markov_ineq (stopped_value M tau) _ Hc Hsv_ge0.
exact: le_trans Hmarkov (optional_stopping HF Hsup Hstop Hcell Hbound).
Qed.

(** [ht_pred M c x k]: predicate that is true when [M k x >= c]. *)
Definition ht_pred (M : nat -> Omega -> R) (c : R)
    (x : Omega) (k : nat) : bool := c <= M k x.

(** [hitting_time M c N x]: the first time [k <= N] at which [M k x >= c],
    or [N] if no such time exists. *)
Definition hitting_time (M : nat -> Omega -> R) (c : R) (N : nat)
    (x : Omega) : nat :=
  minn (find (ht_pred M c x) (iota 0 N.+1)) N.

(** The hitting time is bounded above by the horizon [N]. *)
Lemma hitting_time_bound (M : nat -> Omega -> R) (c : R) (N : nat)
    (x : Omega) :
  (hitting_time M c N x <= N)%N.
Proof. exact: geq_minr. Qed.

(** The hitting time of an adapted process is a stopping time. *)
Lemma hitting_time_stopping (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (c : R) (N : nat) :
  filtration F -> adapted F M ->
  stopping_time F (hitting_time M c N).
Proof.
move=> HF Hadapt n x y Hxy.
rewrite /hitting_time !geq_min.
case HN: (N <= n)%N; first by rewrite !orbT.
rewrite !orbF.
have Hone : forall a b : Omega, F n a b ->
  (find (ht_pred M c a) (iota 0 N.+1) <= n)%N ->
  (find (ht_pred M c b) (iota 0 N.+1) <= n)%N.
  move=> a b Hab Hfa.
  set fa := find (ht_pred M c a) (iota 0 N.+1) in Hfa *.
  have HnN : (n < N)%N by rewrite ltnNge HN.
  have HfaN : (fa < N.+1)%N.
    by rewrite ltnS; exact: leq_trans Hfa (ltnW HnN).
  have Hhas : has (ht_pred M c a) (iota 0 N.+1).
    by rewrite has_find size_iota.
  have Hpf := nth_find 0 Hhas.
  rewrite nth_iota //= in Hpf.
  have Hpb : ht_pred M c b fa.
    by rewrite /ht_pred -(Hadapt fa a b (@filtration_mono F fa n a b HF Hfa Hab)).
  have Hle : (find (ht_pred M c b) (iota 0 N.+1) <= fa)%N.
    rewrite leqNgt; apply/negP => Hlt.
    have Hbf := before_find 0 Hlt.
    have Hnth : nth 0 (iota 0 N.+1) fa = fa by rewrite nth_iota //=.
    by rewrite Hnth /ht_pred in Hbf; rewrite /ht_pred in Hpb; rewrite Hpb in Hbf.
  exact: leq_trans Hle Hfa.
apply/idP/idP; first exact: Hone Hxy.
have [_ Hsym _ _] := HF.
by apply: Hone; rewrite Hsym.
Qed.

(** If the process exceeds [c] at some time within the horizon, then it
    exceeds [c] at the hitting time. *)
Lemma hitting_time_hit (M : nat -> Omega -> R) (c : R) (N : nat)
    (x : Omega) :
  [exists k : 'I_N.+1, c <= M k x] ->
  c <= M (hitting_time M c N x) x.
Proof.
move=> /existsP [k Hk].
set f := find (ht_pred M c x) (iota 0 N.+1).
have Hhas : has (ht_pred M c x) (iota 0 N.+1).
  by apply/hasP; exists (val k); [rewrite mem_iota /= add0n ltn_ord|].
have Hpf := nth_find 0 Hhas.
have HfN : (f < N.+1)%N by move: Hhas; rewrite has_find size_iota.
rewrite nth_iota //= in Hpf.
have -> : hitting_time M c N x = f.
  by rewrite /hitting_time -/f; apply/minn_idPl; rewrite -ltnS.
exact: Hpf.
Qed.

(** Doob's maximal inequality via hitting times:
    [c * Pr(max_{k<=N} M_k >= c) <= E[M_0]]. *)
Lemma doob_maximal_ineq (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (c : R) (N : nat) :
  filtration F -> supermartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall k x, 0 <= M k x) ->
  0 < c ->
  c * @Pr R _ mu (fun x => c <= M (hitting_time M c N x) x) <= Exp (M 0).
Proof.
move=> HF Hsup Hcell Hge0 Hc.
have [Hadapt _] := Hsup.
have Hstop : stopping_time F (hitting_time M c N) by apply: hitting_time_stopping.
have Hbound : forall x, (hitting_time M c N x <= N)%N by move=> ?; apply: hitting_time_bound.
have Hsv_ge0 : forall x0, 0 <= stopped_value M (hitting_time M c N) x0 by move=> x0; exact: Hge0.
exact: le_trans (@markov_ineq (stopped_value M (hitting_time M c N)) _ Hc Hsv_ge0)
                 (optional_stopping HF Hsup Hstop Hcell Hbound).
Qed.

(** ** Submartingale results *)

(** A submartingale has non-decreasing expected value at each step. *)
Lemma submartingale_Exp_mono (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  filtration F ->
  submartingale F M ->
  (forall x, 0 < \sum_(y | F n x y) mu y) ->
  Exp (M n) <= Exp (M n.+1).
Proof.
move=> HF [Hadapt Hsub] Hcell.
apply: (le_trans (y := Exp (cond_exp F (M n.+1) n))).
  rewrite /Exp; apply: ler_sum => x _.
  by apply: ler_wpM2l; [exact: mu_ge0 | exact: Hsub].
by rewrite tower_property.
Qed.

(** A submartingale's expected value at any time [n] is bounded below by its
    initial expected value. *)
Lemma submartingale_Exp_ge0 (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  filtration F ->
  submartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  Exp (M 0) <= Exp (M n).
Proof.
move=> HF Hsub Hcell; elim: n => [|n IH]; first exact: lexx.
apply: (le_trans IH).
exact: (@submartingale_Exp_mono F M n HF Hsub (Hcell n)).
Qed.

(** Markov bound for submartingales: [c * Pr(M_n >= c) <= E[M_n]]. *)
Lemma submartingale_markov (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (c : R) (n : nat) :
  submartingale F M ->
  (forall k x, 0 <= M k x) ->
  0 < c ->
  c * @Pr R _ mu (fun x => c <= M n x) <= Exp (M n).
Proof.
move=> Hsub Hge0 Hc.
exact: (@markov_ineq (M n) _ Hc (Hge0 n)).
Qed.

(** Iterated expectation monotonicity for submartingales: [E[M_n]] is
    non-decreasing in [n]. *)
Lemma submartingale_Exp_le (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n m : nat) :
  filtration F ->
  submartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (n <= m)%N -> Exp (M n) <= Exp (M m).
Proof.
move=> HF Hsub Hcell Hnm.
have [d ->] : exists d, m = (n + d)%N.
  by exists (m - n)%N; rewrite subnKC.
elim: d => [|d IH]; first by rewrite addn0.
by rewrite addnS; apply: le_trans IH _;
  exact: (@submartingale_Exp_mono F M (n + d)%N HF Hsub (Hcell _)).
Qed.

(** Doob's inequality for a non-negative submartingale:
    [c * Pr(M_n >= c) <= E[M_m]] at any [m >= n].  The running-max
    form is the classical Doob inequality; this point form is the
    direct Markov consequence strengthened via submartingale
    expectation monotonicity. *)
Lemma submartingale_doob_inequality (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (c : R) (n m : nat) :
  filtration F ->
  submartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  (forall k x, 0 <= M k x) ->
  0 < c ->
  (n <= m)%N ->
  c * @Pr R _ mu (fun x => c <= M n x) <= Exp (M m).
Proof.
move=> HF Hsub Hcell Hge0 Hc Hnm.
apply: (le_trans (@submartingale_markov F M c n Hsub Hge0 Hc)).
exact: (@submartingale_Exp_le F M n m HF Hsub Hcell Hnm).
Qed.

(** ** Telescoping expectation identity *)

(** Telescoping: the expectation difference across [n] steps decomposes as
    a sum of one-step differences. Pure algebraic identity, requires no
    martingale hypothesis. *)
Lemma Exp_telescope (M : nat -> Omega -> R) (n : nat) :
  Exp (M n) - Exp (M 0) = \sum_(k < n) (Exp (M k.+1) - Exp (M k)).
Proof.
elim: n => [|n IH]; first by rewrite big_ord0 subrr.
by rewrite big_ord_recr /= -IH addrC addrA subrK.
Qed.

(** Symmetric form: the total expectation drop of a process equals the sum
    of its one-step drops. *)
Lemma Exp_telescope_sub (M : nat -> Omega -> R) (n : nat) :
  Exp (M 0) - Exp (M n) = \sum_(k < n) (Exp (M k) - Exp (M k.+1)).
Proof.
rewrite -(opprB (Exp (M n))) Exp_telescope -sumrN.
by apply: eq_bigr => k _; rewrite opprB.
Qed.

(** One-step expectation drop of a supermartingale is non-negative. *)
Lemma supermartingale_one_step_drop (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (k : nat) :
  filtration F ->
  supermartingale F M ->
  (forall x, 0 < \sum_(y | F k x y) mu y) ->
  0 <= Exp (M k) - Exp (M k.+1).
Proof.
move=> HF Hsup Hcell.
rewrite subr_ge0.
exact: (@supermartingale_Exp_mono F M k HF Hsup Hcell).
Qed.

(** Every summand of the telescoping decomposition of a supermartingale is
    non-negative. *)
Lemma supermartingale_telescope_ge0 (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  filtration F ->
  supermartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  0 <= \sum_(k < n) (Exp (M k) - Exp (M k.+1)).
Proof.
move=> HF Hsup Hcell.
apply: sumr_ge0 => k _.
exact: supermartingale_one_step_drop HF Hsup (Hcell k).
Qed.

(** ** Reverse (lower) Markov inequality *)

(** If [X <= B] almost surely and [c < B], the probability that [X >= c]
    admits the lower bound [(E[X] - c) / (B - c)]. Complements the classical
    upper-tail Markov inequality. *)
Lemma markov_ineq_lower (X : Omega -> R) (B c : R) :
  c < B ->
  (forall x, X x <= B) ->
  (Exp X - c) / (B - c) <= @Pr R _ mu (fun x => c <= X x).
Proof.
move=> HcB HXB.
have HBc_pos : 0 < B - c by rewrite subr_gt0.
rewrite ler_pdivrMr //.
(* Goal: Exp X - c <= Pr (c <= X) * (B - c) *)
have Hsum_split : \sum_(x | c <= X x) mu x
                + \sum_(x | ~~ (c <= X x)) mu x = 1.
  transitivity (\sum_x mu x); last exact: mu_sum1.
  by rewrite [RHS](bigID (fun x => c <= X x)) /=.
have Hcompl : \sum_(x | ~~ (c <= X x)) mu x
            = 1 - @Pr R _ mu (fun x => c <= X x).
  rewrite /Pr -Hsum_split.
  by rewrite [X in _ = X - _]addrC addrK.
have Hupper : Exp X <= B * @Pr R _ mu (fun x => c <= X x)
                      + c * \sum_(x | ~~ (c <= X x)) mu x.
  rewrite /Exp (bigID (fun x => c <= X x)) /=.
  apply: lerD.
  - rewrite /Pr mulr_sumr; apply: ler_sum => x _.
    by rewrite [B * _]mulrC; apply: ler_wpM2l; [exact: mu_ge0 | exact: HXB].
  - rewrite mulr_sumr; apply: ler_sum => x.
    rewrite -ltNge => Hxc.
    by rewrite [c * _]mulrC; apply: ler_wpM2l; [exact: mu_ge0 | exact: ltW].
rewrite Hcompl in Hupper.
(* Hupper : Exp X <= B * P + c * (1 - P) *)
have : Exp X - c <= B * @Pr R _ mu (fun x => c <= X x)
                  + c * (1 - @Pr R _ mu (fun x => c <= X x)) - c.
  by rewrite lerD2r.
move=> Hstep.
apply: le_trans Hstep _.
(* Goal: B * P + c * (1 - P) - c <= Pr (c <= X) * (B - c) *)
rewrite mulrBr mulr1 mulrBr.
rewrite (mulrC _ B) (mulrC _ c).
by rewrite addrAC addrA subrK.
Qed.

(** ** Reverse filtrations and reverse supermartingales *)

(** A reverse filtration has equivalence relations at each level that
    become COARSER as the index grows (so [F n] refines [F n.+1]),
    dual to a forward filtration. *)
Definition reverse_filtration (F : nat -> Omega -> Omega -> bool) :=
  [/\ (forall n, reflexive (F n)),
      (forall n, symmetric (F n)),
      (forall n, transitive (F n)) &
      (forall n x y, F n x y -> F n.+1 x y) ].

(** [reverse_supermartingale F M]: [M] is adapted to the reverse
    filtration [F], and the conditional expectation of [M n] given the
    coarser [F n.+1]-cell dominates [M n.+1]. Equivalently, [M n.+1] is
    bounded above by the [F n.+1]-averaged value of [M n]. *)
Definition reverse_supermartingale
    (F : nat -> Omega -> Omega -> bool) (M : nat -> Omega -> R) :=
  adapted F M /\
  forall n x, M n.+1 x <= cond_exp F (M n) n.+1 x.

(** A reverse supermartingale has non-increasing expected value at each
    step, just like a forward supermartingale. The direction is the same;
    only the filtration structure is reversed. *)
Lemma reverse_supermartingale_Exp_mono
    (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  reverse_filtration F ->
  reverse_supermartingale F M ->
  (forall x, 0 < \sum_(y | F n.+1 x y) mu y) ->
  Exp (M n.+1) <= Exp (M n).
Proof.
move=> [Hrefl Hsym Htrans _] [Hadapt Hrsup] Hcell.
apply: (le_trans (y := Exp (cond_exp F (M n) n.+1))).
  rewrite /Exp; apply: ler_sum => x _.
  by apply: ler_wpM2l; [exact: mu_ge0 | exact: Hrsup].
by rewrite (@tower_property_level F (M n) n.+1 Hrefl Hsym Htrans Hcell).
Qed.

(** A reverse supermartingale's expected value at any time [n] is bounded
    above by its initial expected value, by iterated one-step monotonicity. *)
Lemma reverse_supermartingale_Exp_bound
    (F : nat -> Omega -> Omega -> bool)
    (M : nat -> Omega -> R) (n : nat) :
  reverse_filtration F ->
  reverse_supermartingale F M ->
  (forall k x, 0 < \sum_(y | F k x y) mu y) ->
  Exp (M n) <= Exp (M 0).
Proof.
move=> HF Hrsup Hcell; elim: n => [|n IH]; first exact: lexx.
apply: (le_trans _ IH).
exact: (@reverse_supermartingale_Exp_mono F M n HF Hrsup (Hcell n.+1)).
Qed.

End DiscreteVille.

(* Prevent the kernel from unfolding intermediate definitions in
   downstream files — keeps type-checking fast and error messages readable. *)
Strategy 100 [cond_exp Exp stopped_process stopped_value hitting_time].

(** ** Filtration-partition equivalence *)

Section FiltrationPartition.

Variable Omega : finType.

(** [equiv_class E x]: the equivalence class of [x] under relation [E]. *)
Definition equiv_class (E : Omega -> Omega -> bool) (x : Omega) : {set Omega} :=
  [set y | E x y].

(** [equiv_classes E]: the set of all equivalence classes induced by [E]. *)
Definition equiv_classes (E : Omega -> Omega -> bool) : {set {set Omega}} :=
  [set equiv_class E x | x in Omega].

(** Every element belongs to its own equivalence class. *)
Lemma equiv_class_refl (E : Omega -> Omega -> bool) (x : Omega) :
  reflexive E -> x \in equiv_class E x.
Proof. by move=> Hrefl; rewrite inE. Qed.

(** Equivalent elements have equal equivalence classes. *)
Lemma equiv_class_eq (E : Omega -> Omega -> bool) (x y : Omega) :
  reflexive E -> symmetric E -> transitive E ->
  E x y -> equiv_class E x = equiv_class E y.
Proof.
move=> Hrefl Hsym Htrans Hxy; apply/setP => z; rewrite !inE.
apply/idP/idP => H.
- by have Hyx : E y x by [rewrite Hsym]; exact (Htrans _ _ _ Hyx H).
- by exact (Htrans _ _ _ Hxy H).
Qed.

(** The equivalence classes of a reflexive relation cover the entire space. *)
Lemma equiv_class_partition_cover (E : Omega -> Omega -> bool) :
  reflexive E ->
  cover (equiv_classes E) = [set: Omega].
Proof.
move=> Hrefl; apply/setP => x; rewrite in_setT /cover.
apply/bigcupP; exists (equiv_class E x).
  by apply/imsetP; exists x.
by rewrite inE.
Qed.

(** The equivalence classes of an equivalence relation are pairwise disjoint. *)
Lemma equiv_class_partition_trivIset (E : Omega -> Omega -> bool) :
  reflexive E -> symmetric E -> transitive E ->
  trivIset (equiv_classes E).
Proof.
move=> Hrefl Hsym Htrans; apply/trivIsetP => _ _ /imsetP [a _ ->] /imsetP [b _ ->] Hneq.
rewrite -setI_eq0; apply/eqP/setP => z; rewrite !inE.
apply/negbTE/negP => /andP [Ha Hb].
have Hzb : E z b by rewrite Hsym.
by rewrite (equiv_class_eq Hrefl Hsym Htrans (Htrans _ _ _ Ha Hzb)) eqxx in Hneq.
Qed.

(** Every equivalence class is non-empty. *)
Lemma equiv_class_nonempty (E : Omega -> Omega -> bool) (A : {set Omega}) :
  reflexive E -> A \in equiv_classes E -> A != set0.
Proof.
move=> Hrefl /imsetP [x _ ->]; apply/set0Pn; exists x.
by rewrite inE.
Qed.

(** Each [F (n+1)] equivalence class is contained in some [F n] class,
    i.e., finer partitions refine coarser ones. *)
Lemma filtration_refines_partition (F : nat -> Omega -> Omega -> bool) (n : nat) :
  (forall m, reflexive (F m)) -> (forall m, symmetric (F m)) ->
  (forall m, transitive (F m)) ->
  (forall m x y, F m.+1 x y -> F m x y) ->
  forall A, A \in equiv_classes (F n.+1) ->
  exists2 B, B \in equiv_classes (F n) & A \subset B.
Proof.
move=> Hrefl Hsym Htrans Href A /imsetP [a _ ->].
exists (equiv_class (F n) a); first by apply/imsetP; exists a.
by apply/subsetP => y; rewrite !inE => /Href.
Qed.

(** [partition_equiv P x y]: [x] and [y] belong to the same block of
    partition [P]. *)
Definition partition_equiv (P : {set {set Omega}}) (x y : Omega) : bool :=
  [exists A in P, (x \in A) && (y \in A)].

(** The partition equivalence of a covering partition is reflexive. *)
Lemma partition_equiv_refl (P : {set {set Omega}}) :
  cover P = [set: Omega] ->
  reflexive (partition_equiv P).
Proof.
move=> Hcover x; apply/existsP.
have : x \in cover P by rewrite Hcover in_setT.
case/bigcupP => A HA Hx.
by exists A; rewrite HA Hx.
Qed.

(** The partition equivalence is symmetric. *)
Lemma partition_equiv_sym (P : {set {set Omega}}) :
  symmetric (partition_equiv P).
Proof.
move=> x y; rewrite /partition_equiv; apply/idP/idP =>
  /existsP [A /andP [HA /andP [H1 H2]]]; apply/existsP; exists A;
  by apply/andP; split; [| apply/andP; split].
Qed.

(** The partition equivalence of a trivIset partition is transitive. *)
Lemma partition_equiv_trans (P : {set {set Omega}}) :
  trivIset P ->
  transitive (partition_equiv P).
Proof.
move=> Htriv y x z /existsP [A /andP [HA /andP [HxA HyA]]]
                     /existsP [B /andP [HB /andP [HyB HzB]]].
have HAB : A = B.
  apply/eqP; apply: contraT => Hneq.
  have /trivIsetP/(_ A B HA HB Hneq) := Htriv.
  rewrite -setI_eq0 => /eqP/setP/(_ y).
  by rewrite !inE HyA HyB.
apply/existsP; exists A; apply/andP; split; first exact: HA.
by apply/andP; split; [exact: HxA | rewrite HAB].
Qed.

(** Round-trip: partitioning by [E] then recovering the equivalence yields
    exactly [E]. *)
Lemma partition_equiv_roundtrip (E : Omega -> Omega -> bool) (x y : Omega) :
  reflexive E -> symmetric E -> transitive E ->
  partition_equiv (equiv_classes E) x y = E x y.
Proof.
move=> Hrefl Hsym Htrans; apply/idP/idP.
- move=> /existsP [A /andP [/imsetP [z _ ->] /andP [Hx Hy]]].
  by rewrite !inE in Hx Hy; rewrite Hsym in Hx; exact (Htrans _ _ _ Hx Hy).
- move=> Hxy; apply/existsP; exists (equiv_class E x).
  apply/andP; split; first by apply/imsetP; exists x.
  by apply/andP; split; rewrite inE.
Qed.

End FiltrationPartition.

(** ** Partition-derived filtrations *)

(** A refining partition sequence induces a valid filtration via
    [partition_equiv].  This bridges the partition-based view of
    information refinement (common in discrete probability textbooks)
    to the equivalence-relation-based formulation used by the
    supermartingale theory in [DiscreteVille].  Once [partition_filtration]
    produces a [filtration], all results — Ville's inequality, optional
    stopping, Doob's maximal inequality — apply unchanged. *)

Section PartitionFiltration.

Variable Omega : finType.

Lemma partition_filtration (P : nat -> {set {set Omega}}) :
  (forall n, cover (P n) = [set: Omega]) ->
  (forall n, trivIset (P n)) ->
  (forall n A, A \in P n.+1 -> exists2 B, B \in P n & A \subset B) ->
  @filtration Omega (fun n => partition_equiv (P n)).
Proof.
move=> Hcover Htriv Hrefine; split.
- by move=> n; exact: partition_equiv_refl.
- by move=> n; exact: partition_equiv_sym.
- by move=> n; exact: partition_equiv_trans.
- move=> n x y /existsP [A /andP [HA /andP [HxA HyA]]].
  have [B HB Hsub] := Hrefine n A HA.
  apply/existsP; exists B; apply/andP; split; first exact: HB.
  by apply/andP; split; apply: (subsetP Hsub).
Qed.

End PartitionFiltration.

(** ** Downstream example: discrete partition yields filtration *)

(** The discrete partition (singletons) is constant and refining,
    so [partition_filtration] produces a valid filtration.  This
    witnesses that [partition_filtration] fires on a concrete input. *)
Lemma discrete_partition_filtration (Omega : finType) :
  @filtration Omega (fun n => partition_equiv [set [set x] | x in Omega]).
Proof.
apply: partition_filtration => [n|n|n A HA].
- apply/setP => x; rewrite in_setT /cover.
  apply/bigcupP; exists [set x]; last by rewrite inE.
  by apply/imsetP; exists x.
- apply/trivIsetP => _ _ /imsetP [a _ ->] /imsetP [b _ ->] /negP Hne.
  rewrite -setI_eq0; apply/eqP/setP => z; rewrite !inE.
  apply/andP; case => /eqP -> /eqP Hab.
  by apply: Hne; rewrite Hab.
- by exists A; [exact: HA | apply/subsetP].
Qed.

(* --- Bibliography ---

   tower_property:
     A. N. Kolmogorov, Grundbegriffe der Wahrscheinlichkeits-
     rechnung, Springer, Berlin, 1933.  English translation:
     Foundations of the Theory of Probability, Chelsea, 1950.
     (Rigorous conditional expectation and tower property.)
     J. L. Doob, Stochastic Processes, John Wiley & Sons,
     New York, 1953, Ch. VII.  ISBN: 978-0-471-52369-7.

   markov_ineq:
     P. L. Chebyshev, "Des valeurs moyennes," J. Math. Pures
     Appl., 2e série, 12:177-184, 1867.  (Implicit method.)
     A. A. Markov, Wahrscheinlichkeitsrechnung, Teubner,
     Leipzig, 1912.  (General statement.)

   ville_ineq, ville_step_bound, ville_stopping:
     J. Ville, Étude critique de la notion de collectif,
     Gauthier-Villars, Paris, 1939.

   optional_stopping, stopped_process_supermartingale:
     J. L. Doob, Stochastic Processes, Wiley, 1953, Ch. VII.

   doob_maximal, doob_maximal_ineq:
     J. L. Doob, Stochastic Processes, Wiley, 1953, Ch. VII.

   partition_filtration, partition_equiv_roundtrip,
   filtration_refines_partition:
     Standard equivalence-relation / partition duality.
     No specific published source.
*)

Print Assumptions ville_ineq.
Print Assumptions tower_property.
Print Assumptions optional_stopping.
Print Assumptions ville_stopping.
Print Assumptions doob_maximal.
Print Assumptions stopped_process_supermartingale.
Print Assumptions partition_equiv_roundtrip.
