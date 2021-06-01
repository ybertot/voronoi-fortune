From mathcomp Require Import all_ssreflect all_algebra all_field.
From mathcomp Require Import all_real_closed.
From mathcomp.analysis Require Import classical_sets posnum topology
  normedtype landau sequences boolp reals ereal.
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

Lemma times2_continuous : continuous (fun w : R => 2%:R * w).
Proof.
have ctn : continuous (fun w : R => w *+ 2).
    exact: natmul_continuous.
move=>x; rewrite mulr_natl.
have -> // : [eta *%R 2%:R] = (GRing.natmul (V :=R))^~ 2%nat.
by apply: funext=> y; rewrite mulr_natl.
Qed.

Lemma times2_constinuous' : continuous (fun w : R => 2%:R * w).
Proof.
move=> y.
apply: cvgMr.
apply: cvg_id.
Qed.

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

Lemma inverse_increasing_continuous (a b k : R) (f g : R -> R) :
  a < b ->
  0 < k ->
  {in (g @` [set x | x \in `]a, b[ ])%classic, continuous f} ->
  {in (g @` [set x | x \in `]a, b[ ])%classic &,
       forall x y, x < y -> k * (y - x) < f y - f x} ->
  {in `]a, b[, cancel g f} ->
  {in `]a, b[, continuous g}.
Proof.
move=> altb kgt0 ctf incrf gK y ayb.
apply/cvg_distP=> _ /posnumP[e].
rewrite !near_simpl /=; near=> x.
(*
have xltb : x < b.
  near: x.
  have it := near_shift 0 y (fun u => u < b).
  rewrite near_simpl it; near=> z.
  rewrite /= subr0 addrC -ltr_subr_addl.
  apply: ltr_normlW.
  by near:z; apply: nbhs0_lt; rewrite subr_gt0; case/andP: ayb.
have xgta : a < x.
  near: x.
  have it := near_shift 0 y (fun u => a < u).
  rewrite near_simpl it; near=> z.
  rewrite /= subr0 addrC. 
  rewrite -ltr_subl_addr -ltr_subr_addl.
  apply: ltr_normlW; rewrite normrN.
  by near:z; apply: nbhs0_lt; rewrite subr_gt0; case/andP:ayb.
have axb : x \in `]a, b[ by apply/andP.
*)
have : g y < g x -> g x - g y < e%:num.
  near: x.
  have it := near_shift 0 y (fun u => g y < g u -> g u - g y <e%:num).
  rewrite near_simpl it; near=> z.
  rewrite /= subr0.
  have : z < b - y.
    apply: ltr_normlW.
    by near: z; apply: nbhs0_lt; rewrite subr_gt0; case/andP: ayb.
  rewrite ltr_subr_addr => zin.
  have : a - y < z.
    rewrite ltr_subl_addr -ltr_subl_addl -ltr_subr_addl.
    apply: ltr_normlW; rewrite normrN.
    by near: z; apply: nbhs0_lt; rewrite subr_gt0; case/andP: ayb.
  rewrite ltr_subl_addr => zin'.
  have gzin : g (z + y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists (z + y)=> //; apply/andP.
  have gyin : g (y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists y.
  move/incrf=> /(_ gyin gzin); rewrite !gK //; last by apply/andP.
  rewrite addrK -ltr_pdivl_mull //; move/lt_trans; apply.
  rewrite mulrC lter_pdivr_mulr //; apply: ltr_normlW.
  by near: z; apply: nbhs0_lt; apply: mulr_gt0.
have : g x < g y -> g y - g x < e%:num.
  near: x.
  have it := near_shift 0 y (fun u => g u < g y -> g y - g u <e%:num).
  rewrite near_simpl it; near=> z.
  rewrite /= subr0.
  have : z < b - y.
    apply: ltr_normlW.
    by near: z; apply: nbhs0_lt; rewrite subr_gt0; case/andP: ayb.
  rewrite ltr_subr_addr => zin.
  have : a - y < z.
    rewrite ltr_subl_addr -ltr_subl_addl -ltr_subr_addl.
    apply: ltr_normlW; rewrite normrN.
    by near: z; apply: nbhs0_lt; rewrite subr_gt0; case/andP: ayb.
  rewrite ltr_subl_addr => zin'.
  have gzin : g (z + y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists (z + y)=> //; apply/andP.
  have gyin : g (y) \in ([set g u | u in [set x | x \in `]a, b[]])%classic.
    by rewrite inE /=; exists y.
  move/incrf=> /(_ gzin gyin); rewrite !gK //; last by apply/andP.
  rewrite opprD addrA addrAC addrN sub0r.
  rewrite -ltr_pdivl_mull //; move/lt_trans; apply.
  rewrite mulrC lter_pdivr_mulr //; apply: ltr_normlW; rewrite normrN.
  by near: z; apply: nbhs0_lt; apply: mulr_gt0.
move=> main1 main2.
have [ gxltgy | ] := boolP(g x < g y).
  move: (gxltgy); rewrite -(subr_gt0 (g x)) => case1.
  by rewrite gtr0_norm // main1.
rewrite -leNgt le_eqVlt=> /orP[/eqP -> | gyltgx].
  by rewrite subrr normr0.
move: (gyltgx); rewrite -(subr_lt0 (g x)) => case2.
by rewrite ltr0_norm // opprB main2.
Grab Existential Variables. all: end_near. Qed.

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

