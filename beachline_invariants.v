Require Import String.
From mathcomp Require Import all_ssreflect all_algebra all_field.
Require Import QArith.
From Coq Require Extraction.

Import GRing.Theory Num.Theory Num.ExtraDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import fortune.

Section invariants.

Variable R : rcfType.

Notation pick_sol a b :=
  (fortune.pick_sol 1%R (@GRing.add _) (@GRing.mul _)
      (@GRing.opp _) (@GRing.inv _) sqrtr (@eq_op _)
      Order.le (@GRing.natmul _) (@GRing.exp _) a b).

Fixpoint breakpoints (bl : seq (arc R)) (swp : R) : seq R :=
  match bl with
    nil => nil
  | _ :: nil => nil
  | a1 :: (a2 :: _) as tl =>
       pick_sol (focal a1) (focal a2) swp :: breakpoints tl swp
  end.

Definition inv1 bl swp := sorted Order.le (breakpoints bl swp).

Notation circumcenter := (circumcenter (@GRing.one R) (@GRing.add _)
      (@GRing.mul _) (@GRing.opp _) (@GRing.inv _) (@GRing.natmul _)).

Notation collinear := (collinear (@GRing.add _)
      (@GRing.mul _) (@GRing.opp _) (@eq_op _)).

Definition dist (p1 p2 : point R) :=
  sqrtr ((coordx  p1 - coordx p2) ^+ 2  + (coordy  p1 - coordy p2) ^+ 2).

Fixpoint top_circles (bl : seq (arc R)) : seq R :=
  match bl with
  | nil => nil
  | _ :: nil => nil
  | _ :: _ :: nil => nil
  | a1 :: (a2 :: a3 :: _) as tl =>
    if collinear (focal a1) (focal a2) (focal a3) then
      top_circles tl
    else
      let p := circumcenter (focal a1) (focal a2) (focal a3) in
      (coordy p + dist (focal a1) p)%R :: top_circles tl
  end.

Fixpoint circle_events (bl : seq (arc R)) (swp : R) :=
  filter [pred x | (swp < x)%R] (top_circles bl).

Lemma circle_events_cons (a1 a2 a3 : arc R) (bl : seq (arc R)) (swp : R) :
  circle_events [:: a1, a2, a3 & bl] swp =
  if collinear (focal a1) (focal a2) (focal a3) then
     circle_events [:: a2, a3 & bl] swp
  else
    let p := (circumcenter (focal a1) (focal a2) (focal a3)) in
    if (swp < (coordy p + dist (focal a1) p))%R then
  (coordy p + dist (focal a1) p)%R :: 
  circle_events [:: a2, a3 & bl] swp else
  circle_events [:: a2, a3 & bl] swp.
Proof. by rewrite /=; case: ifP. Qed.

Lemma inv1_cons a1 a2 a3 bl swp :
  inv1 [:: a1, a2, a3 & bl] swp = 
  (pick_sol (focal a1) (focal a2) swp <=
    pick_sol (focal a2) (focal a3) swp)%R &&
  inv1 [:: a2, a3 & bl] swp.
Proof. by []. Qed.

Lemma inv1_no_circle bl swp swp' :
  (forall x, (swp < x < swp')%R ->
       ~~ (x \in (circle_events bl swp))) ->
  inv1 bl swp -> inv1 bl swp'.
Proof.
elim: bl => [ | a1 [ | a2 [ | a3 bl']] IH] // ncc hinv.
have /IH IH': forall x, (swp < x < swp')%R ->
            x \notin circle_events [:: a2, a3 & bl'] swp.
  move=> x /ncc; rewrite circle_events_cons /=.
  move=> abs1; apply/negP=> xin; case/negP: abs1; case: ifP=> // _.
  by case: ifP=> // _; rewrite inE xin orbT.
rewrite inv1_cons IH' ?andbT; last by move: hinv; rewrite inv1_cons=> /andP[].

