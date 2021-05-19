Require Import String.
From mathcomp Require Import all_ssreflect all_algebra all_field.
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

Definition p_x (pt : R ^ 2) :=
  pt (Ordinal (isT : (0 < 2)%nat)).

Definition p_y (pt : R ^ 2) :=
  pt (Ordinal (isT : (1 < 2)%nat)).

Lemma pt_eqP p q : reflect (p = q) ((p_x p == p_x q) && (p_y p == p_y q)).
Proof.
have [/eqP xxs | nxxs] := boolP (_ == _);
  have [/eqP yys | nyys ] := boolP (_ == _); constructor;
  try (move=> abs; (try move: nxxs); (try move: nyys); rewrite abs eqxx //).
- apply/ffunP=> [] [ [ | [ | z]] // pp].
  * by rewrite (@val_inj _ _ _ (Ordinal pp) (Ordinal (isT : 0 < 2)%N)).
  * by rewrite (@val_inj _ _ _ (Ordinal pp) (Ordinal (isT : 1 < 2)%N)).
Qed.

Definition parabola (px py s : R) : {poly R} :=
  ((s + px) /2 %:R)%:P -
   ((py%:P - 'X) ^+ 2) * ((2 %:R * (s - px)) ^-1)%:P.

Definition parabola' p s y := (parabola (p_x p) (p_y p) s).[y].

Definition parabola0 p s :=
  (s + p_x p) / 2%:R - p_y  p ^+ 2 / (2%:R * (s - p_x p)).

Definition parabola1 p s :=
  (p_y p) / (s - p_x p).

Definition parabola2 p s :=
  - (2%:R * (s - p_x p)) ^-1.

Lemma parabolacE p s :
   parabola (p_x p) (p_y p) s =
   (parabola0 p s)%:P + (parabola1 p s)%:P * 'X +
   (parabola2 p s)%:P * 'X ^+ 2.
Proof.
rewrite /parabola sqrrB.
rewrite (mulrDl _ _ ((_ ^-1)%:P)) (mulrBl ((_ ^-1)%:P)) -polyC_exp -polyCM.
rewrite 2!opprD opprK 2!addrA -polyCB; congr (_ + _ + _).
rewrite -mulrnAl mulrAC; congr (_ * _).
  by rewrite -polyCMn -polyCM -mulr_natl -mulf_div mulfV ?mul1r // pnatr_eq0.
by rewrite mulrC -mulNr -polyCN.
Qed.

Lemma parabolaE px py s y :
  (parabola px py s).[y] =
  ((s + px) / 2%:R) - ((py - y) ^+ 2) / (2%:R * (s - px)).
Proof. by rewrite /parabola !hornerE. Qed.

Definition beachline (pts : seq (R ^ 2)) s (y : R) : R :=
  if [seq p <- pts | p_x p < s] is q :: pts' then
    \big[Order.max/(parabola (p_x q) (p_y q) s).[y]]_(p <- pts')
      (parabola (p_x p) (p_y p) s).[y]
  else 0.

Definition sq_dist (a b : R ^ 2) : R :=
  (p_x a - p_x b) ^+ 2 + (p_y a - p_y b) ^+ 2.

Lemma sq_distC a b : sq_dist a b = sq_dist b a.
Proof.
by rewrite /sq_dist -(opprB (p_x a)) -(opprB (p_y a)) !sqrrN.
Qed.

Lemma parabolaP q p s :
  p_x p < s ->
  p_x q < s ->
  (p_x p < (parabola (p_x q) (p_y q) s).[p_y p]) =
  (sq_dist q p < (s - p_x p) ^+ 2).
Proof.
move=> half_plane_p half_plane_q.
rewrite /sq_dist.
remember ((p_y q - p_y p) ^+ 2) as w1.
rewrite addrC !sqrrB.
rewrite !addrA lter_add2.
rewrite [in RHS]ltr_sub_addr .
rewrite  -!(mulr_natr (_ * p_x p)) -mulNr -(addrA (s ^+ 2)) -mulrDl.
rewrite (addrC (- _)) -(opprB _ (p_x q * p_x p)) mulNr.
rewrite -mulrBl.
rewrite [in RHS]ltr_sub_addr.
rewrite (mulrAC _ (p_x p)).
rewrite !(addrAC _ _ (_ * p_x p)) (addrC _ (_ * p_x p)).
rewrite -2!ltr_subr_addr.
rewrite subr_sqr.
have half_plane' : 0 < s - p_x q by rewrite subr_gt0.
rewrite -lter_pdivl_mull; last first.
  by apply: mulr_gt0; rewrite // ltr0Sn.
rewrite -(mulrC 2%:R) invfM -mulrA.
rewrite mulrBr.
rewrite  mulrA mulVf ?mul1r; last first.
  by move: half_plane'; rewrite lt_neqAle eq_sym=>/andP[] ->.
rewrite mulrDr (mulrC (2%:R ^-1)).
rewrite mulrN mulrA -invfM (mulrC _ w1).
by rewrite parabolaE Heqw1.
Qed.

Lemma big_max_eq_idx (e q : R ^ 2) (F : R ^ 2 -> R) l :
  Order.max (F q) (\big[Order.max/F e]_(r <- l) F r) =
  Order.max (F e) (\big[Order.max/F q]_(r <- l) F r).
Proof.
elim: l e q => [ | r l Ih] e q.
  by rewrite !big_nil maxC.
by rewrite !big_cons !(maxCA _ (F r)) Ih.
Qed.

Lemma big_max_ge_idx (e : R ^ 2) (F : R ^ 2 -> R) l :
  F e <= \big[Order.max/F e]_(r <- l) F r.
Proof.
elim: l => [ | p l Ih]; first by rewrite big_nil le_refl.
by rewrite big_cons le_maxr Ih orbT.
Qed.

Lemma big_max_ge_in (e q : R ^ 2) (F : R ^ 2 -> R) l :
  q \in l -> F q <= (\big[Order.max/F e]_(r <- l) F r).
Proof.
elim: l => [ | q' l Ih] //=.
rewrite inE big_cons=> /orP[/eqP <- | ]; first by rewrite le_maxr le_refl.
by move=> qin; rewrite le_maxr Ih ?orbT.
Qed.

Lemma big_max_rem l e q (F : R ^ 2 -> R) :
  q \in l ->
  \big[Order.max/F e]_(r <- l) F r =
  Order.max (F e) (\big[Order.max/F q]_(r <- rem q l) F r).
Proof.
elim: l q => [ // | r l Ih] q.
rewrite inE=> qin.
rewrite big_cons.
have [qr | qnotr] := boolP(q == r).
  by rewrite /= eq_sym qr (eqP qr) big_max_eq_idx.
move: qin; rewrite (negbTE qnotr) /= => qin.
rewrite eq_sym (negbTE qnotr).
by rewrite (Ih _ qin) big_cons maxCA.
Qed.

Lemma filterC (T : Type) (p1 p2 : pred T) (l : seq T) :
  [seq e <- [seq e <- l | p1 e] | p2 e] =
  [seq e <- [seq e <- l | p2 e] | p1 e].
Proof.
by elim:l => [ | e l Ih] //=; case: ifP => vp1 /=; case: ifP => vp2 /=;
  rewrite Ih ?vp1.
Qed.

Lemma rem_filter' (T : eqType) (p : pred T) (l : seq T) (e : T) :
  rem e [seq x <- l | p x] = [seq x <- rem e l | p x].
Proof.
elim: l => [| a l Ih] //=; case: ifP => pa /=; case: ifP=> ae /=;
  rewrite ?pa ?Ih //.
move: pa; rewrite (eqP ae)=> pe {ae Ih}.
elim: l => [ | b l Ih] //=.
case: ifP.
  by move/eqP => ->; rewrite pe.
by move => be /=; case: ifP; rewrite Ih.
Qed.

Lemma beachline_pivot q pts s :
  q \in pts -> p_x q < s -> beachline pts s =1 beachline (q :: rem q pts) s.
Proof.
case: pts => [// | q' pts].
move=> qpt qin y.
rewrite /beachline /= qin.
have [q'in | q'notin] := ifP.
  have [/eqP -> // | qnq'] := ifP.
  have qin' : q \in [seq p <- pts | p_x p < s].
    by move: qpt; rewrite mem_filter qin inE eq_sym qnq' /=.
  rewrite (big_max_rem _ _ qin') /= q'in big_cons.
  congr (Num.max _ (\big[_/_]_(_ <- _) _)).
  by rewrite rem_filter'.
have qnq' : (q'== q)%B = false.
  have [qq' | //] := boolP (q'== q).
  by move: q'notin; rewrite (eqP qq') qin.
rewrite qnq' /= q'notin.
have notempty : q \in [seq p <- pts | p_x p < s].
  by move: qpt; rewrite inE eq_sym qnq' /= mem_filter qin => ->.
have [q2 [pts' vq2]] : {q2 : R ^ 2 & {pts' : seq (R ^ 2) |
         [seq p <- pts | p_x p < s] = [:: q2 & pts' ]}}.
  case filter_eq : [seq p <- pts | p_x p < s] => [ | q2 pts'].
    by move: notempty; rewrite filter_eq.
  by exists q2, pts'.
rewrite vq2.
set x := (LHS).
have -> : x =
   \big[Num.max/(parabola (p_x q2) (p_y q2) s).[y]]_(p <- q2 :: pts')
          (parabola (p_x p) (p_y p) s).[y].
  by rewrite big_cons maxEle big_max_ge_idx.
rewrite <- vq2.
rewrite (big_max_rem _ _ notempty).
rewrite rem_filter'.
have [q2inrem |q2notinrem] := boolP(q2 \in [seq x0 <- rem q pts | p_x x0 < s]).
  by rewrite maxEle big_max_ge_in.
rewrite -rem_filter' vq2 /=.
case: ifP => [/eqP -> | _].
  by rewrite maxEle big_max_ge_idx.
by rewrite maxEle big_max_ge_in ?inE ?eqxx.
Qed.

Lemma beachlineP pts s y :
  [seq p <- pts | p_x p < s] != [::] ->
  {p : R ^ 2 | (p \in [seq p <- pts | p_x p < s]) &&
   (beachline pts s y ==
     (parabola (p_x p) (p_y p) s).[y]) &&
   all (fun w => (parabola (p_x w) (p_y w) s).[y] <=
                 (parabola (p_x p) (p_y p) s).[y])
       [seq p <- pts | p_x p < s]}.
Proof.
rewrite /beachline.
case : [seq p0 <- pts | p_x p0 < s] => [ | q pts'] // _.
elim: pts' => [ | q' pts' [v /andP [/andP [vin /eqP vval] /= /andP[qlev Ih]]]].
  by exists q; rewrite inE big_nil !eqxx all_seq1 le_refl.
rewrite big_cons vval.
have vin' : v \in q :: q' :: pts'.
  by move: vin; rewrite !inE => /orP[] ->; rewrite ?orbT.
case: (lerP (parabola (p_x q') _ _).[y] (parabola (p_x v) _ _).[y])
   => [q'le | q'ge].
  by exists v; rewrite eqxx /= q'le qlev Ih vin'.
exists q'.
  rewrite !inE !eqxx orbT le_refl ?andbT /=.
have -> /=:
  (parabola (p_x q) (p_y q) s).[y] <= (parabola (p_x q') (p_y q') s).[y].
  by apply: le_trans (ltW q'ge).
apply/allP=> w win; apply: le_trans (ltW q'ge).
rewrite -vval.
by apply: big_max_ge_in.
Qed.

Fixpoint intersect_poly_aux (pt1 : R ^ 2) (pts : seq (R ^ 2)) (swp : R)
  (acc : {poly R}) : {poly R} :=
  match pts with
  | nil => acc
  | pt2 :: tl => ((parabola (p_x pt1) (p_y pt1) swp) -
            (parabola (p_x pt2) (p_y pt2) swp))  *
           intersect_poly_aux pt1 tl swp acc
  end.

Fixpoint intersect_poly (pts : seq (R ^ 2)) (swp : R) : {poly R} :=
  match pts with
  | nil => 1
  | a :: tl => intersect_poly_aux a tl swp (intersect_poly tl swp)
  end.

Lemma intersect_poly_aux_accP p pts swp P y :
(* question why can't I use the notation y \in root P *)
  root P y -> root (intersect_poly_aux p pts swp P) y.
Proof.
elim: pts => [ | p2 tl Ih] //.
by move=> yr /=; rewrite rootM Ih ?orbT.
Qed.

Lemma intersect_poly_auxP p pts swp P :
  {in pts, forall p2, forall y,
  (parabola' p swp y == parabola' p2 swp y) ->
  root (intersect_poly_aux p pts swp P) y}.
Proof.
elim: pts P => [ | p2 tl Ih] // P.
move=> p'; rewrite inE=> /orP[/eqP p'p2 | p'np2].
  rewrite p'p2 {p' p'p2} /parabola' => y /eqP pyp2y /=.
  rewrite rootM; apply/orP; left.
  by apply/rootPt; rewrite hornerE pyp2y hornerN subrr.
move=> y pyp'y /=.
rewrite rootM; apply/orP; right.
by apply: (Ih P _ p'np2).
Qed.

Lemma intersect_polyP pts swp :
  {in pts &, forall p1 p2, p1 <> p2 -> forall y,
    parabola' p1 swp y == parabola' p2 swp y ->
    root (intersect_poly pts swp) y}.
Proof.
elim: pts => [ | p tl Ih] //= p1 p2; rewrite !inE => /orP [/eqP p1p | p1tl].
  rewrite p1p=> /orP[/eqP p2p | p2tl]; first by rewrite p2p.
  by move=> _ y; apply: intersect_poly_auxP.
move=>/orP [/eqP p2p | p2tl].
   move=> _ y; rewrite p2p {p2 p2p} eq_sym => poleq.
   by apply: (intersect_poly_auxP _ _ poleq).
move=> p1np2 y polyeq.
apply: intersect_poly_aux_accP.
by apply: (Ih p1 p2).
Qed.

Lemma parabola_inj p1 p2 swp :
  p_x p1 != swp -> p_x p2 != swp ->
  (p1 == p2) =
   (parabola (p_x p1) (p_y p1) swp ==
    parabola (p_x p2) (p_y p2) swp).
Proof.
move=> ns1 ns2.
apply/idP/idP.
  by move=> /eqP ->; rewrite eqxx.
rewrite /parabola mulrBr.
(* Here I wish to decompose the equality between polynomials into a
  series of of equalities for each coefficient, but the coefficients
  are hidden in uses of polyC. *)
rewrite !sqrrB.
rewrite ![(_ + 'X^2) * _]mulrDl !mulrBl -!(mulr_natr (_ * _) 2).
rewrite -!polyC_exp -!polyCM.
rewrite [in X in X == _]opprD [in X in _ == X]opprD !opprB !addrA.
rewrite [in X in X == _](addrAC (polyC _)).
rewrite [in X in _ == X](addrAC (polyC _)) -!polyCB.
rewrite !(mulrC ('X ^ 2)) !(mulrAC _ 'X).
rewrite !mulr_natr -!polyCMn -!polyCM.
rewrite -subr_eq0 !opprD !opprK !addrA.
rewrite !(addrAC _ _ (-(polyC _))) -polyCB.
rewrite !(addrAC _ _ (- (_ * 'X))) -(addrA (polyC _)) -(mulNr _ 'X).
rewrite -mulrDl -polyCN -polyCD -(addrA _ (- (_ * 'X ^ 2))).
rewrite -(mulNr _ ('X ^ 2)) -mulrDl -polyCN -polyCD.
set A := (A in A%:P + _ + _).
set B := (B in _ + B%:P * 'X + _).
set C := (C in _ + _ + C%:P * 'X ^ 2).
rewrite !mul_polyC.
move=>/eqP pol_eq.
have xs : p_x p1 = p_x p2.
  have : (0 : {poly R})`_2 = 0 by rewrite coef0.
  rewrite -pol_eq !coefD !coefZ coefC coefX coefXn /= mulr1 mulr0 !add0r.
  rewrite /C addrC=> /eqP; rewrite subr_eq0 (inj_eq invr_inj).
  rewrite -mulrBr (inj_eq (mulfI _)); last by rewrite pnatr_eq0.
  by rewrite (inj_eq (addrI _)) (inj_eq oppr_inj) eq_sym=>/eqP.
have ys : p_y p1 = p_y p2.
  have : (0 : {poly R})`_1 = 0 by rewrite coef0.
  rewrite -pol_eq !coefD !coefZ coefC coefX coefXn /= mulr1 mulr0 add0r addr0.
  rewrite /B addrC=> /eqP; rewrite subr_eq0.
  rewrite -mulrBr xs (inj_eq (mulIf _)); last first.
    rewrite invr_eq0 mulf_eq0 negb_or subr_eq0 [in X in _ && X]eq_sym ns2.
    by rewrite pnatr_eq0.
  by rewrite (inj_eq (pmulrnI _)) // => /eqP.
by apply/eqP/pt_eqP; rewrite xs ys !eqxx.
Qed.

Lemma intersect_poly_aux_non0 p pts swp P :
  uniq pts -> p \notin pts -> P != 0 ->
  p_x p != swp -> all (fun p2 => p_x p2 != swp) pts ->
  intersect_poly_aux p pts swp P != 0.
Proof.
elim: pts => [ | p2 tl Ih]; first by [].
rewrite inE /= negb_or => /andP[] p2nin utl /andP[] pnp2 pnin Pn0 pns.
move=> /andP[] p2ns allns.
rewrite mulf_eq0 negb_or; apply/andP; split; last by apply: Ih.
by rewrite subr_eq0 -parabola_inj.
Qed.

(* This is a candidate for automated proofs, especially to
 be seen with people interested in AI. *)
Lemma intersect_poly_non0 pts swp :
  uniq pts -> all (fun p => p_x p != swp) pts ->
  intersect_poly pts swp != 0.
Proof.
elim: pts => [ | p pts Ih]; first by rewrite /= oner_neq0.
rewrite /= => /andP[] pnotin upts /andP[] pns allns.
by apply: intersect_poly_aux_non0=> //; apply: Ih.
Qed.

Fixpoint discrete_beachline_aux (swp : R) (sites : seq (R ^ 2))
   (front_sites : seq (R ^ 2)) (intersections : seq R)
   (lower_bound : R) (first_arc : R ^ 2) :=
  match front_sites, intersections with
  | nil, nil =>
    forall y : R, lower_bound <= y ->
       beachline sites swp y = parabola' first_arc swp y
  | f1 :: front_sites, i1 :: intersections =>
    (forall y : R, lower_bound <= y <= i1 ->
       beachline sites swp y = parabola' first_arc swp y) /\
    discrete_beachline_aux swp sites front_sites intersections i1 f1
  | _, _ => False
  end.

Definition discrete_beachline (swp : R) (sites : seq (R ^ 2))
  (front_sites : seq (R ^ 2)) : Prop :=
  (size sites = 1%N /\ front_sites = sites) \/
  (0 < size front_sites)%N /\
  (exists (i0 : R) (intersections : seq R),
    forall y, y < i0 ->
      beachline sites swp y =
      parabola' (nth [ffun x => 0] front_sites 0) swp y /\
      discrete_beachline_aux swp sites  (behead front_sites)
        intersections i0 (nth [ffun x => 0] front_sites 0)).

Definition solve_snd_degreep (a b c : R) :
  0 < a -> (exists x, (c%:P + b%:P * 'X + a%:P * 'X ^+ 2).[x] < 0) ->
 {r1 & {r2 | r1 < r2 /\
   (c%:P + b%:P * 'X + a%:P * 'X ^ 2).[r1] = 0 /\
   (c%:P + b%:P * 'X + a%:P * 'X ^ 2).[r2] = 0 /\
   (forall x, x < r1 \/ r2 < x -> 0 < (c%:P + b%:P * 'X + a%:P * 'X ^ 2).[x]) /\
   (forall x, r1 < x < r2 -> (c%:P + b%:P * 'X + a%:P * 'X ^ 2).[x] < 0) /\
   r1 = (- b - Num.sqrt (b ^+ 2 - a * c *+ 4)) / (a *+ 2) /\
   r2 = (- b + Num.sqrt (b ^+ 2 - a * c *+ 4)) / (a *+ 2)}}.
move=> apos negval.
set r1 := (- b - Num.sqrt (b ^+ 2 - a * c *+ 4)) / (a *+ 2).
set r2 := (- b + Num.sqrt (b ^+ 2 - a * c *+ 4)) / (a *+ 2).
exists r1, r2.
set l3 := (X in X.[_]); rewrite -/l3.
have an0 : a != 0.
  by move: apos; rewrite lt_neqAle eq_sym=>/andP[].
move:negval; rewrite -/l3.
have two_vap : 0 < (a *+ 2) ^-1 by rewrite invr_gt0 pmulrn_rgt0.
have l3eq : l3 = a%:P * (('X + (b / (a *+ 2))%:P) ^+ 2 -
                    ((b ^+ 2 - a * c *+ 4) / ((a *+ 2) ^+ 2) )%:P).
  rewrite sqrrD !mulrDr -!addrA addrC /l3; congr (_ + _).
  rewrite !mulrA !(mulrAC _ 'X) !addrA -mulr2n -2!mulrnAl -polyCM -polyCMn.
  rewrite -addrA addrC; congr (_ + _).
    rewrite -mulr_natl -(mulr_natl a) invfM !mulrA !(mulrAC _ _ (2%:R ^-1)).
    by rewrite mulfV ?mul1r ?pnatr_eq0 // mulrAC mulfV ?mul1r.
  rewrite -polyCM mulrN -polyCM -polyCB.
  rewrite -mulrA -[X in _ = (_ * X - _)%:P]/((b / (a *+ 2)) ^+ 2).
  rewrite expr_div_n mulrBl mulrBr opprD opprK addrA addrN add0r.
  have -> : (a *+ 2) ^+ 2 = a ^+ 2 *+ 4.
    rewrite -mulr_natl -(mulr_natl a) exprS expr1 mulrA (mulrAC _ _ 2%:R).
    by rewrite -natrM -mulrA; congr (_ * _).
  rewrite !mulrA -mulrnAl invfM !mulrA !(mulrAC _ _ (a ^-1)) mulfV // mul1r.
  by rewrite mulrAC mulfV ?mul1r // mulrn_eq0.
rewrite l3eq; move=> negval.
have discr_pos : 0 < b ^+2 - a * c *+ 4.
  move: negval => [w]; rewrite !(horner_exp, hornerE).
  rewrite pmulr_rlt0 // subr_lt0=> Pw.
  have sqgt0 : 0 < (a *+ 2) ^- 2.
    by rewrite invr_gt0 exprn_gt0 // pmulrn_rgt0.
  rewrite -(pmulr_lgt0 _ sqgt0).
  by apply: le_lt_trans Pw; apply: sqr_ge0.
have frac_sqrt : ((b ^ 2 - a * c *+ 4) / ((a *+ 2) ^+ 2)) =
                 (Num.sqrt (b ^ 2 - a * c *+ 4) / (a *+ 2)) ^+ 2.
  by rewrite expr_div_n sqr_sqrtr ?ltW.
split.
  rewrite /r1 /r2 lter_pmul2r; last by rewrite invr_gt0 pmulrn_rgt0.
  by rewrite ltr_add2l gt0_cp // sqrtr_gt0.
split.
  rewrite !(horner_exp, hornerE) /r1.
  rewrite [X in (X + _) ^+2 - _]mulrBl addrAC mulNr addNr add0r sqrrN.
  by rewrite -frac_sqrt addrN mulr0.
split.
  rewrite !(horner_exp, hornerE) /r2.
  rewrite [X in (X + _) ^+2 - _]mulrDl addrAC mulNr addNr add0r.
  by rewrite expr_div_n sqr_sqrtr ?addrN ?mulr0 // ltW.
split.
  move=> x xout.
  rewrite !(horner_exp, hornerE) pmulr_rgt0 //.
  rewrite frac_sqrt subr_sqr.
  move: xout => [xlow | xhigh].
    rewrite nmulr_lgt0 //.
      rewrite subr_lte0 -ltr_subr_addr (lt_le_trans xlow) //.
      rewrite /r1 mulrBl addrC mulNr ler_add2r ge0_cp // mulr_ge0 // ltW //.
      by rewrite sqrtr_gt0.
    set w := Num.sqrt _ / _; rewrite -(addNr w) lter_add2 -(add0r (-w)).
    set w' := _ / _; rewrite -(addNr w') addrAC lter_add2.
    by rewrite /w' /w -mulNr -mulrBl.
  rewrite pmulr_lgt0 //.
     by rewrite subr_gt0 -ltr_subl_addr addrC -mulNr -mulrDl.
  rewrite -ltr_subl_addr sub0r -ltr_subl_addr addrC (le_lt_trans _ xhigh) //.
  rewrite /r2 mulrDl -mulNr ler_add2l ge0_cp // mulr_ge0 // ltW //.
  by rewrite sqrtr_gt0.
split.
  move=> x /andP [r1low r2high].
  rewrite !(horner_exp, hornerE) nmulr_llt0 // frac_sqrt subr_sqr.
  rewrite nmulr_rlt0 -addrA.
    by rewrite -ltr_subl_addr add0r -mulrDl -mulNr opprD.
  by rewrite -ltr_sub_addr add0r -mulrBl -mulNr opprD opprK.
by [].
Qed.

Lemma parabola_max p swp :
  (parabola (p_x p) (p_y p) swp).[p_y p] = (swp + p_x p) / 2%:R.
Proof.
rewrite /parabola hornerD hornerN hornerM horner_exp hornerD hornerN hornerX.
by rewrite !hornerC subrr expr0n /= mul0r subr0.
Qed.

Lemma parabola_maxP p swp y :
  p_x p < swp ->
  (parabola (p_x p) (p_y p) swp).[y] <= (swp + p_x p) / 2%:R.
Proof.
move=> plt.
rewrite /parabola hornerD hornerN hornerM horner_exp hornerD hornerN hornerX.
rewrite !hornerC ler_subl_addr ler_addl.
rewrite mulr_ge0 ?sqr_ge0 // invr_ge0 mulr_ge0 ?ler0n //.
by rewrite subr_ge0 ltW.
Qed.

Lemma parabola_diff_reorg p1 p2 swp :
  parabola (p_x p1) (p_y p1) swp - parabola (p_x p2) (p_y p2) swp =
  (parabola0 p1 swp - parabola0 p2 swp)%:P +
  (parabola1 p1 swp - parabola1 p2 swp)%:P * 'X +
  (parabola2 p1 swp - parabola2 p2 swp)%:P * 'X ^+ 2.
Proof.
have reorg a b c d e f g h : (a + b * g + c * h) - (d + e * g + f * h) =
   (a - d) + (b - e) * g + (c - f) * h.
  by rewrite !mulrBl !opprD !addrA 2!(addrAC _ _ (-d)) (addrAC _ _ (-(e * _))).
by rewrite !parabolacE reorg -!polyCB.
Qed.

Lemma parabola_diff_min p1 p2 swp :
  p_x p1 < p_x p2 < swp ->
  parabola' p1 swp (p_y p2)  < parabola' p2 swp (p_y p2).
Proof.
move=> /andP[] p1p2 p2swp.
rewrite /parabola' parabola_max.
apply: le_lt_trans (_ : ((swp + p_x p1) / 2%:R) < _).
  by apply/parabola_maxP/(lt_trans p1p2).
rewrite ltr_pmul2r; last by rewrite invr_gt0 ltr0Sn.
by rewrite ltr_add2l.
Qed.

Definition par_inter (p1 p2 : R ^ 2) (swp : R) :
  p_x p1 < swp -> p_x p2 < swp ->
  {v : R | (p_x p1 != p_x p2) ->
     (parabola' p1 swp v = parabola' p2 swp v) /\
     (exists a b, a < v < b /\
       (forall x, a < x < v -> parabola' p2 swp x < parabola' p1 swp x) /\
       (forall x, v < x < b -> parabola' p1 swp x < parabola' p2 swp x))}.
move=> p1lt p2lt.
(* FIXME: figure out how to use wlog here.
wlog : p1 p2 p2lt p1lt p1np2 / p_x p1 < p_x p2.
  move=> one_side.
have [p1ltp2 /=| ] := boolP (p_x p1 < p_x p2); first by apply: one_side.
  rewrite -leNgt le_eqVlt.
  have [ //= | p1np2x] := boolP (p_x p1 == p_x p2).
  rewrite eq_sym (negbTE p1np2x) /= => p2ltp1.
*)
have [p1ltp2 | ] := boolP(p_x p1 < p_x p2).
  have tmp : exists x,
    ((parabola0 p1 swp - parabola0 p2 swp)%:P +
     (parabola1 p1 swp - parabola1 p2 swp)%:P * 'X +
     (parabola2 p1 swp - parabola2 p2 swp)%:P * 'X ^+ 2).[x] < 0.
    exists (p_y p2).
    rewrite -parabola_diff_reorg hornerD hornerN subr_lt0.
    by rewrite parabola_diff_min // p1ltp2.
  have tmp2 : 0 < parabola2 p1 swp - parabola2 p2 swp.
    rewrite subr_gt0 /parabola2 ltr_oppr opprK ltf_pinv ?posrE /=.
        rewrite ltr_pmul2l; last by rewrite ltr0Sn.
        by rewrite ltr_add2l ltr_oppr opprK.
      by rewrite mulr_gt0 // ?ltr0Sn ?subr_gt0.
    by rewrite mulr_gt0 // ?ltr0Sn ?subr_gt0.
  have [r1 [r2 [r1r2 [root1 [root2 [outi [ini _]]]]]]] :=
       solve_snd_degreep tmp2 tmp.
  exists r1=> _; split.
    apply/eqP; rewrite -subr_eq0.
    by rewrite /parabola' -hornerN -hornerD parabola_diff_reorg root1.
  exists (r1 - 1); exists r2.
  split.
    by rewrite r1r2 ltr_subl_addl cpr_add ltr01.
  split.
    move=> x /andP[_ xltr1].
    rewrite -subr_gt0.
    by rewrite /parabola' -hornerN -hornerD parabola_diff_reorg outi //; left.
  move=> x xint.
  rewrite -subr_lt0.
    by rewrite /parabola' -hornerN -hornerD parabola_diff_reorg ini.
rewrite -leNgt le_eqVlt eq_sym.
have [dummy //= | p1np2x /= ] := boolP(p_x p1 == p_x p2).
  by exists 0.
move=> p2ltp1.
have tmp : exists x,
    ((parabola0 p2 swp - parabola0 p1 swp)%:P +
     (parabola1 p2 swp - parabola1 p1 swp)%:P * 'X +
     (parabola2 p2 swp - parabola2 p1 swp)%:P * 'X ^+ 2).[x] < 0.
  exists (p_y p1).
  rewrite -parabola_diff_reorg hornerD hornerN subr_lt0.
  by rewrite parabola_diff_min // p2ltp1.
have tmp2 : 0 < parabola2 p2 swp - parabola2 p1 swp.
  rewrite subr_gt0 /parabola2 ltr_oppr opprK ltf_pinv ?posrE /=.
      rewrite ltr_pmul2l; last by rewrite ltr0Sn.
      by rewrite ltr_add2l ltr_oppr opprK.
    by rewrite mulr_gt0 // ?ltr0Sn ?subr_gt0.
  by rewrite mulr_gt0 // ?ltr0Sn ?subr_gt0.
have [r1 [r2 [r1r2 [root1 [root2 [outi [ini _]]]]]]] :=
   solve_snd_degreep tmp2 tmp.
exists r2 => _.
split.
  apply/eqP; rewrite eq_sym -subr_eq0.
  by rewrite /parabola' -hornerN -hornerD parabola_diff_reorg root2.
exists r1; exists (r2 + 1).
split.
  by rewrite r1r2 cpr_add ltr01.
split.
  move=> x xint.
  rewrite -subr_lt0.
  by rewrite /parabola' -hornerN -hornerD parabola_diff_reorg ini.
move=> x /andP [xgtr2 _].
rewrite -subr_gt0.
by rewrite /parabola' -hornerN -hornerD parabola_diff_reorg outi //; right.
Qed.

Lemma parabola_compare_low (p1 p2 : R ^ 2) (swp : R) :
  p_x p1 < p_x p2 < swp ->
  exists i, forall y, y < i -> parabola' p2 swp y < parabola' p1 swp y.
Proof.
move=> /andP [p1p2 p2swp].
have p1swp : 0 < swp - p_x p1 by rewrite subr_gt0; apply: lt_trans p2swp.
move: (p2swp); rewrite -subr_gt0=> p2swp'.
have dumb2 : 0 < (2%:R : R) by rewrite ltr0Sn.
have diff_degp : 0 < parabola2 p1 swp - parabola2 p2 swp.
  rewrite /parabola2 subr_gt0.
  rewrite ltr_oppl opprK ltf_pinv ?posrE ?mulr_gt0 // ltr_pmul2l //.
  by rewrite ltr_add2l ltr_oppl opprK.
have tmp : exists x,
  ((parabola0 p1 swp - parabola0 p2 swp)%:P +
   (parabola1 p1 swp - parabola1 p2 swp)%:P * 'X +
   (parabola2 p1 swp - parabola2 p2 swp)%:P * 'X ^+ 2).[x] < 0.
  exists (p_y p2).
  rewrite -parabola_diff_reorg hornerD hornerN subr_lt0.
  by rewrite parabola_diff_min // p1p2.
have [r1 [r2 [_ [_ [_ [outi  _]]]]]] := solve_snd_degreep diff_degp tmp.
exists r1=> y yltr1; rewrite -subr_gt0 /parabola' -hornerN -hornerD.
by rewrite parabola_diff_reorg outi //; left.
Qed.

Lemma first_bl_element (swp : R) (sites : seq (R ^ 2)) (e : R ^ 2) :
  p_x e < swp ->
  all (fun p => p_x e < p_x p) sites ->
  exists i0,
   forall y,  y < i0 ->
     beachline (e :: sites) swp y = parabola' e swp y.
Proof.
move=> ein; elim: sites => [ | p sites Ih].
  by move=> _; exists 0=> y _; rewrite /beachline /= ein big_nil.
move=> /= /andP[] eltp allgt; rewrite /beachline /= ein.
case: ifP => [pin | pnin]; last first.
  move: (Ih allgt) => [i0 Ih'].
  exists i0; move=> y ilt /=.
  by rewrite -(Ih' y ilt) /beachline /= ein.
have : p_x e < p_x p < swp by rewrite eltp pin.
move/parabola_compare_low => [i below_i].
have [i'] := Ih allgt.
rewrite /beachline /= ein => below_i'.
exists (Order.min i i') => y; rewrite lt_minr=>/andP[] ylti ylti'.
by rewrite big_cons below_i' // maxEle ltW // below_i.
Qed.
