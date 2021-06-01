From mathcomp Require Import all_ssreflect all_algebra all_field.
From mathcomp Require Import all_real_closed.
From mathcomp.analysis Require Import boolp reals classical_sets topology
  normedtype.
(* Require Import QArith. *)
From Coq Require Extraction.

Import GRing.Theory Num.Theory Num.ExtraDef.
Import Order.POrderTheory Order.TotalTheory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section rcf_sandbox.

Variable R : rcfType.

Lemma normM (x y : R) : `| x * y | = `|x| * `|y|.
Proof.
by rewrite normrM.
Qed.

End rcf_sandbox.

Section sandbox.

Variable R : realType.

Lemma times2_continuous_epsilon_delta : continuous (fun x : R => 2%:R * x).
Proof.
move=> x B /nbhs_ballP [e Pe be].
apply/nbhs_ballP; exists (e / 2%:R).
  by rewrite /= divr_gt0 ?ltr0Sn.
move=> y /= ynearx; apply:be.
(* Hard to guess this step: ball is convertible to a norm comparison. *)
rewrite -[ball  _ _ _]/(_ (_ < _)).
rewrite -mulrBr.
by rewrite normrM normr_nat -ltr_pdivl_mull // mulrC.
Qed.

Lemma times2_continuous : continuous (fun w : R => 2%:R * w).
Proof.
have ctn : continuous (fun w : R => w *+ 2).
    exact: natmul_continuous.
move=> x.
rewrite mulr_natl.
move=> S /ctn FS.
suff: (2%:R * w @[w --> x] --> w *+2 @[w -->x])%classic.
  by apply; exact: FS.
Admitted.

Lemma times2_constinuous' : continuous (fun w : R => 2%:R * w).
Proof.
move=> y.
apply: cvgMr.
apply: cvg_id.
Qed.

Lemma sqrt_continuous : {in [pred x | 0 < x], continuous (@Num.sqrt R)}.
Proof.
move=> x.
rewrite inE=> xgt0 B /nbhs_ballP [e Pe be].
apply/nbhs_ballP; exists ((2%:R * Num.sqrt x) ^-1).
  by rewrite /= invr_gt0 mulr_gt0 // sqrtr_gt0.
move=> y /= ynearx.
apply: be.

Set Printing All.
Print continuous.
Variable x : R.

Check topology.numFieldTopology.real_topologicalType R.

