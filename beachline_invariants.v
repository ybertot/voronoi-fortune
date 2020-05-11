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

Notation pick_sol :=
  (pick_sol (@GRing.one R) (@GRing.add _) (@GRing.mul _)
      (@GRing.opp _) (@GRing.inv _) sqrtr (@eq_op _)
      Order.le (@GRing.natmul _) (@GRing.exp _)).

Fixpoint breakpoints (bl : seq (arc R)) (swp : R) : seq R :=
  match bl with
    nil => nil
  | _ :: nil => nil
  | a1 :: (a2 :: _) as tl =>
       pick_sol (focal a1) (focal a2) swp :: breakpoints tl swp
  end.
