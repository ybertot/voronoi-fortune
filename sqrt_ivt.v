From mathcomp Require Import all_ssreflect all_algebra all_field.
From mathcomp Require Import all_real_closed.
(* Require Import QArith. *)
From Coq Require Extraction.

Import GRing.Theory Num.Theory Num.ExtraDef.
Import Order.POrderTheory Order.TotalTheory.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section math_view.

Open Scope ring_scope.

Variables (R : rcfType).

Lemma sqrt_ivt_base  (p1 p2 p3 : {poly R}) (a b : R):
   (forall x, a <= x <= b -> 0 <= p1.[x]) ->
   (forall x, a <= x <= b -> p2.[x] <= 0) ->
   (forall x, a <= x <= b -> 0 <= p3.[x]) ->
   a <= b -> p1.[a] + p2.[a] * Num.sqrt p3.[a] <= 0 <=
             p1.[b] + p2.[b] * Num.sqrt p3.[b] ->
   exists2 x, a <= x <= b &
       p1.[x] + p2.[x] * Num.sqrt p3.[x] = 0.
Proof.
move=> p1ge0 p2le0 p3ge0 aleb sign_condition.
set p := p1 ^+ 2 - p2 ^+ 2 * p3.
have peq x : a <= x <= b -> p.[x] =
  (p1.[x] - p2.[x] * Num.sqrt p3.[x]) *
  (p1.[x] + p2.[x] * Num.sqrt p3.[x]).
  move=> intx; rewrite -subr_sqr exprMn_comm; last by rewrite /GRing.comm mulrC.
  rewrite sqr_sqrtr; last by apply: p3ge0.
  by rewrite -!horner_exp -hornerM -hornerN -hornerD.
have factxge0 x : a <= x <= b -> 0 <= p1.[x] - p2.[x] * Num.sqrt p3.[x].
  move=> intx; apply: addr_ge0; rewrite ?p1ge0 // -mulNr mulr_ge0 //.
    by rewrite oppr_ge0 p2le0.
  by rewrite sqrtr_ge0.
have fact0impp0 x : a <= x <= b ->
  p1.[x] - p2.[x] * Num.sqrt p3.[x] = 0 -> p1.[x] = 0 /\
     p2.[x] * Num.sqrt p3.[x]= 0.
  move=> intx /eqP.
  rewrite subr_eq0=> /eqP facta0.
  have p10 : p1.[x] = 0.
    apply: le_anti.
    by rewrite p1ge0 // facta0 mulr_le0_ge0 // ?p2le0 ?sqrtr_ge0.
  by rewrite p10 -facta0 p10.  
have sign_condition' : p.[a] <= 0 <= p.[b].
  have aab : a <= a <= b by rewrite lexx aleb.  
  have abb : a <= b <= b by rewrite lexx aleb.  
  apply/andP; split.
    rewrite peq // mulr_ge0_le0 // ?factxge0 //.
    by move/andP:sign_condition=> [].
  rewrite peq // mulr_ge0 // ?factxge0 //.
  by move/andP: sign_condition=> [].
have [r Pr1 Pr2] := poly_ivt aleb sign_condition'.
exists r=> //.
move: Pr2; rewrite /root peq // mulf_eq0 => /orP[] /eqP //.
by move/(fact0impp0 _ Pr1)=>[] -> ->; rewrite addr0.
Qed.
