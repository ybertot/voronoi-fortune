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
  ((s + px) / 2%:R)%:P -
   ((py%:P - 'X) ^+ 2) * ((2 %:R * (s - px)) ^-1)%:P.

Definition pbl (px py s : R) : {poly R} :=
  (s ^+ 2 - px ^ 2)%:P - ((py%:P - 'X) ^+ 2).

Definition parabola' p s y := (parabola (p_x p) (p_y p) s).[y].

Definition pbl' p s y := (pbl (p_x p) (p_y p) s).[y].

Definition pbl0 p s :=
    s ^+ 2 - p_x p ^+ 2 - p_y p ^+ 2.

Definition parabola0 p s :=
  (s + p_x p) / 2%:R - p_y  p ^+ 2 / (2%:R * (s - p_x p)).

Definition pbl1 (p : R ^ 2) (s : R) :=  2%:R * p_y p.

Definition parabola1 p s :=
  (p_y p) / (s - p_x p).

Definition pbl2 (p : R ^ 2) (s : R) : R := -1.

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

Lemma pblcE p s :
  pbl (p_x p) (p_y p) s =
  (pbl0 p s)%:P + (pbl1 p s)%:P * 'X + (pbl2 p s)%:P * 'X^2.
Proof.
rewrite /pbl sqrrB -polyC_exp 2!opprD opprK 2!addrA -polyCB.
congr (_ + _ + _).
  by rewrite -mulrnAl; congr (_ * _); rewrite -polyCMn -mulr_natl.
by rewrite /pbl2 polyCN polyC1 mulNr mul1r.
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
  {p : R ^ 2 |
   ([seq p <- pts | p_x p < s] != [::]) ==>
   ((p \in [seq p <- pts | p_x p < s]) &&
   (beachline pts s y ==
     (parabola (p_x p) (p_y p) s).[y]) &&
   all (fun w => (parabola (p_x w) (p_y w) s).[y] <=
                 (parabola (p_x p) (p_y p) s).[y])
       [seq p <- pts | p_x p < s])}.
Proof.
rewrite /beachline.
case : [seq p0 <- pts | p_x p0 < s] => [ | q pts'] //.
   by exists [ffun _ => 0].
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
  | _, _ => Logic.False
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

Lemma descartes_zero (p : {poly R}) :
 (forall k, 0 <= p`_k) ->
 (exists i, 0 < p`_i) ->
 (forall y, 0 < y -> 0 < p.[y]) /\
 (forall x y, 0 < x < y -> p.[x] <= p.[y]).
Proof.
move: (p : seq R) (polyseqK p)=> ps; move: p; elim: ps.
  by move=> p pnil pos_coef [] i; rewrite nth_nil ltxx.
move=> a q Ih p paq poss [wp Pwp].
  have [/(has_nthP 0) [i _ Pi]| allzero] := boolP(has (fun x => 0 < x) q).
  have poss' : forall k, 0 <= q`_k by move=> k; move: (poss k.+1).
  have [posq incrq] := Ih _ erefl poss' (ex_intro _ i Pi).
  split.
    move=> y ygt0; rewrite -paq /= horner_cons ltr_paddr //.
      by apply: (poss 0%N).
    by rewrite mulr_gt0 // posq.
  move=> x y /andP[xgt0 xlty].
  rewrite -paq /= !horner_cons lter_add2.
  have : (Poly q).[y] * x <= (Poly q).[y] * y.
    by rewrite lter_pmul2l // ?posq // ?(lt_trans xgt0 xlty) ?ltW.
  have : (Poly q).[x] * x <= (Poly q).[y] * x.
    by rewrite lter_pmul2r // incrq // xgt0 xlty.
  by apply: le_trans.
have poss' : forall k, 0 <= q`_k by move=> k; exact: (poss k.+1).
have qis0 : forall y, (Poly q).[y] = 0.
  clear -allzero poss'.
  move/hasPn: allzero => allzero.
  elim: q allzero poss'=> [ | a q Ih] allzero poss.
    by move=>y; rewrite horner0.
  move=> y; rewrite /= horner_cons (_ : a = 0); last first.
    move: (allzero a) (poss 0%N) => /=; rewrite inE eqxx /=.
    by rewrite le_eqVlt=> /(_ isT) /negbTE ->; rewrite orbF=> /eqP <-.
  rewrite addr0 Ih ?mul0r //.
    by move=> c cin; apply: (allzero c); rewrite inE cin orbT.
  by move=> k; apply: (poss k.+1).
have wpis0 : wp = 0%N.
  move: Pwp; case: wp=>[// | wp /= abs].
  case/hasP: allzero; exists (q`_wp) => //.
  have [/(nth_default 0) is0 | ] := boolP(size q <= wp)%N.
    by move: abs; rewrite lt_neqAle is0 eqxx.
   by rewrite -ltnNge=> /mem_nth.
rewrite -paq /=; split.
  by move=> y; rewrite horner_cons qis0 mul0r add0r; move: Pwp; rewrite wpis0.
by move=> x y; rewrite !horner_cons !qis0  !mul0r !add0r lexx.
Qed.

Lemma descartes_one (p : {poly R}) (n : nat) :
  (forall k, (k < n)%N -> p`_k <= 0) ->
  (forall k, (n <= k)%N -> 0 <= p`_k) ->
  (exists i, p`_i < 0) ->
  (exists i, 0 < p`_i) ->
  exists a, 0 < a /\ p.[a] = 0 /\
      (forall y, 0 < y < a -> p.[y] < 0) /\
      (forall y, a < y -> 0 < p.[y]).
Proof.
move=> h1 h2 h3 h4.
suff [a [agt0 [aroot [neg [pos incr]]]]] : exists a, 0 < a /\ p.[a] = 0 /\
         (forall y, 0 < y < a -> p.[y] < 0) /\
         (forall y, a < y -> 0 < p.[y]) /\
         (forall x y, a < x < y -> p.[x] <= p.[y]).
  by exists a; split;[ | split;[ |split ]].
move: (polyseq p) (esym (polyseqK p)) h1 h2 h3 h4 =>s; move: p n.
elim: s=> [ | c0 q Ih] p n ->.
  by move=> _ _ [] i; rewrite nth_nil ltxx.
move=> negs poss [wn Pwn] [wp Pwp].
have ngtwn : (wn < n)%N.
  by rewrite ltnNge; apply/negP=>/poss; rewrite leNgt Pwn.
have negs' : forall k, (k < n.-1)%N -> q`_k <= 0.
  move=> k kn.
  have kn' : (k.+1 < n)%N by rewrite -(ltn_predK ngtwn) ltnS.
  by apply: (negs k.+1).
have poss' : forall k, (n.-1 <= k)%N -> 0 <= q`_k.
  move=> k nk.
  have nk' : (n <= k.+1)%N by rewrite -(ltn_predK ngtwn) ltnS.
  by apply: (poss k.+1).
have wpgt0 : (0 < wp)%N.
  have [wp0 |//] := posnP.
  have /negs : (wp < n)%N by apply: leq_ltn_trans ngtwn; rewrite wp0.
  by rewrite leNgt Pwp.
have [/eqP constant0 | constantnot0] := boolP(c0 == 0).
  rewrite constant0 /=.
  have wngt0 : (0 < wn)%N.
    by have [wn0 |//] := posnP; move: Pwn; rewrite wn0 constant0 ltxx.
  have exn : exists i, q`_i < 0.
    by exists wn.-1; move: Pwn; rewrite -(ltn_predK wngt0).
  have exp : exists i, 0 < q`_i.
    by exists wp.-1; move: Pwp; rewrite -(ltn_predK wpgt0).
  have [a [agt0 [roota [sub0 [sup0 incr]]]]] :=
     Ih (Poly q) n.-1 erefl negs' poss' exn exp.
  exists a; split; [by [] | ].
  split; [by rewrite horner_cons roota mul0r add0r |].
  split.
    move=> y /andP [ygt0 ylta]; rewrite horner_cons addr0.
    by rewrite nmulr_rlt0 // sub0 // ygt0 ylta.
  split.
    move=> y ygta; rewrite horner_cons addr0.
    by rewrite pmulr_rgt0 ?(lt_trans agt0 ygta) // sup0.
  move=> x y /andP[xgta ygtx]; rewrite !horner_cons !addr0.
  have : (Poly q).[y] * x <= (Poly q).[y] * y.
    by rewrite lter_pmul2l // ?sup0 // ?(lt_trans xgta ygtx) ?ltW.
  have : (Poly q).[x] * x <= (Poly q).[y] * x.
    by rewrite lter_pmul2r // ?incr // ?xgta ?ygtx // (lt_trans agt0 xgta).
  by apply: le_trans.
have c0neg : c0 < 0.
  have /negs : (0 < n)%N by apply: leq_ltn_trans ngtwn.
  by rewrite le_eqVlt (negbTE constantnot0).
have exp : exists w, 0 < q`_w.
  by exists wp.-1; move: Pwp; rewrite -(ltn_predK wpgt0).
have [/hasP [c1 c1in c1neg] | /hasPn allpos] := boolP (has (fun c => c < 0) q).
  set wn' := index c1 q.
  have exn : exists w, q`_w < 0.
    by exists wn'; rewrite nth_index.
  move: Ih=>Ih.
  have [a [agt0 [roota [sub0 [sup0 incr]]]]] :=
  Ih (Poly q) n.-1 erefl negs' poss' exn exp.
  set d := (Poly q).[a + 1].
  set a' := a + 1 - c0 / d.
  have dgt0 : 0 < d by apply:sup0; rewrite cpr_add ltr01.
  have cd0_gt0 : 0 < - (c0 / d).
    by rewrite -mulNr divr_gt0 // oppr_gt0.
  have qaged : d <= (Poly q).[a'].
    by apply: incr; rewrite cpr_add ltr01 cpr_add.
  have a'pos : 0 < (Poly (c0 :: q)).[a'].
    rewrite /= horner_cons.
    rewrite mulrDr -addrA ltr_paddr //; last first.
      rewrite mulr_gt0 //; last by rewrite (lt_trans agt0) // cpr_add ltr01.
      by apply: lt_le_trans qaged.
    rewrite -ler_subl_addr sub0r (@le_trans _ _ (d * -(c0 / d))) //.
    rewrite mulrN mulrC mulfVK //.
      by move: dgt0; rewrite lt_neqAle eq_sym=> /andP[].
    by rewrite ler_pmul2r.
  have alta' : a < a'.
    by rewrite /a' -addrA cpr_add addr_gt0.
  have pa_lt0 : (Poly (c0 :: q)).[a] < 0.
    by rewrite horner_cons roota mul0r add0r.
    have signchange : (Poly (c0 :: q)).[a] <= 0 <= (Poly (c0 :: q)).[a'].
    by rewrite !ltW.
  have [r /andP[] rgea _ /rootP Pr] := poly_ivt (ltW alta') signchange.
  have rgta : a < r.
    move: rgea; rewrite le_eqVlt=> /orP[ |//].
    by move/eqP=> ar; move: pa_lt0; rewrite -Pr ar !ltxx.
  exists r; split.
    by apply: lt_le_trans rgea.
  split.
    exact: Pr.
  split.
    move=> y /andP [ygt0 yltr].
    have [ | ] := boolP (y <= a).
      rewrite le_eqVlt=> /orP[/eqP -> // | ylta].
      rewrite /= horner_cons.
      by rewrite ltr_snsaddl // ?pmulr_llt0 ?sub0 // ?ygt0.
    rewrite -ltNge=> ygta.
    rewrite -Pr /= !horner_cons ltr_add2r.
    rewrite (@le_lt_trans _ _ ((Poly q).[r] * y)) //.
      by rewrite ler_pmul2r ?incr ?yltr ?ygta.
    by rewrite ltr_pmul2l // sup0.
  split.
    move=> y ygtr; rewrite -Pr /= !horner_cons ltr_add2r.
    rewrite (@le_lt_trans _ _ ((Poly q).[y] * r)) //.
      by rewrite ler_pmul2r ?incr // ?rgta // (lt_trans agt0 rgta).
    by rewrite ltr_pmul2l // sup0 // (lt_trans rgta ygtr).
  move=> x y /andP[xgtr ygt] /=.
  have xgta : a < x by apply: lt_trans xgtr.
  have xgt0 : 0 < x by apply: lt_trans xgta.
  rewrite !horner_cons ler_add2r (@le_trans _ _ ((Poly q).[y] * x)) //.
    by rewrite ler_pmul2r // incr // xgta ygt.
  by rewrite ler_pmul2l ?(ltW ygt) // sup0 // (lt_trans xgta).
have allpos' : forall k, 0 <= (Poly q)`_k.
  move=> k; have [kin | def] := boolP(k < size q)%N; last first.
  by rewrite coef_Poly nth_default // leqNgt.
  by rewrite coef_Poly leNgt; apply: allpos; rewrite mem_nth.
have exp' : exists i, 0 < (Poly q)`_i.
  by move: exp=> [w wP]; exists w; rewrite coef_Poly.
have [sup0 incr] := descartes_zero allpos' exp'.
set d := (Poly q).[1].
set a' := 1 - c0 / d.
have dgt0 : 0 < d by apply:sup0; rewrite ltr01.
have cd0_gt0 : 0 < - (c0 / d).
  by rewrite -mulNr divr_gt0 // oppr_gt0.
have qaged : d <= (Poly q).[a'].
  by apply: incr; rewrite ltr01 cpr_add.
have a'pos : 0 < (Poly (c0 :: q)).[a'].
  rewrite /= horner_cons.
  rewrite mulrDr -addrA ltr_paddr //; last first.
    by rewrite mulr_gt0 ?ltr01 //; apply: lt_le_trans qaged.
  rewrite -ler_subl_addr sub0r (@le_trans _ _ (d * -(c0 / d))) //.
  rewrite mulrN mulrC mulfVK //.
    by move: dgt0; rewrite lt_neqAle eq_sym=> /andP[].
  by rewrite ler_pmul2r.
have a'gt0 : 0 < a' by rewrite addr_gt0 ?ltr01.
have p0_lt0 : (Poly (c0 :: q)).[0] < 0 by rewrite horner_cons mulr0 add0r.
have signchange : (Poly (c0 :: q)).[0] <= 0 <= (Poly (c0 :: q)).[a'].
  by rewrite !ltW.
have [r /andP[] rge0 _ /rootP Pr] := poly_ivt (ltW a'gt0) signchange.
have rgt0 : 0 < r.
  move: rge0; rewrite le_eqVlt=> /orP[ |//].
  by move/eqP=> ris0; move: p0_lt0; rewrite -[X in _ < X]Pr -ris0 !ltxx.
exists r; split=> //.
split; first by exact: Pr.
split.
  move=> y /andP [ygt0 yltr].
  rewrite -Pr /= !horner_cons ltr_add2r.
  rewrite (@le_lt_trans _ _ ((Poly q).[r] * y)) //.
    by rewrite ler_pmul2r ?incr ?yltr ?ygt0.
  by rewrite ltr_pmul2l // sup0.
split.
  move=> y ygtr; rewrite -Pr /= !horner_cons ltr_add2r.
  rewrite (@le_lt_trans _ _ ((Poly q).[y] * r)) //.
    by rewrite ler_pmul2r ?incr // ?rgta // ?rgt0.
  by rewrite ltr_pmul2l // sup0 ?(lt_trans rgt0 ygtr).
move=> x y /andP[xgtr ygt] /=.
have xgt0 : 0 < x by apply: lt_trans xgtr.
rewrite !horner_cons ler_add2r (@le_trans _ _ ((Poly q).[y] * x)) //.
  by rewrite ler_pmul2r // incr // xgt0 ygt.
by rewrite ler_pmul2l ?(ltW ygt) // sup0 // (lt_trans xgt0).
Qed.

Definition pre_beachline_sites (pts : seq (R ^ 2)) (swp : R) : seq (R ^ 2) :=
  let pts' := [seq p <- pts | p_x p < swp] in
  if pts' == [::] then
     [::]
  else let roots := rootsR (intersect_poly pts swp) in
  if roots is a :: tl then
    map (fun x => proj1_sig (beachlineP pts swp x))
      ((a - 1) :: map (fun p => (p.1 + p.2) / 2%:R) (zip roots tl) ++
             [:: last a tl + 1])
  else
    [::].

Fixpoint remove_head (T : eqType) (a : T) (s : seq T) : seq T :=
  match s with
  | b :: s' => if a == b then remove_head a s' else s
  | _ => s
  end.

Lemma remove_headP (T : eqType) (a : T) s b tl :
  remove_head a s = b :: tl -> a != b.
Proof.
elim: s b tl => [ | c tl' Ih] b tl //=.
case: ifP=> [aisc | aisnc].
  by apply: Ih.
by move=> [] <- tl'tl; rewrite aisnc.
Qed.

Lemma const_map (T T' : Type) (a : T) (l l' : seq T') :
  size l = size l' -> [seq a | _ <- l] =  [seq a | _ <- l'].
Proof.
by elim: l l' => [ | c l Ih] [ | c' l'] //= /eqP; rewrite eqSS=>/eqP/Ih ->.
Qed.

Lemma remove_head0P (T : eqType) (a : T) s :
  reflect (exists n, s = mkseq (fun=> a) n) (remove_head a s == [::]).
Proof.
have [it | notit] := boolP(_ == _).
  apply: ReflectT.
elim: s it => [ | a' s Ih /=]; first by exists 0%N.
  case: ifP=> [/eqP <- | //] /Ih [n ->]; exists n.+1.
  by rewrite /mkseq //=; congr (_ :: _); apply: const_map; rewrite !size_iota.
apply: ReflectF.
elim: s notit=> [// | b s Ih /=].
case: ifP=> [/eqP <- | anb].
  move/Ih=> abs [[// | n] Pn]; case: abs; exists n.
  move: Pn; rewrite /mkseq /= => [[]] ->.
  by apply: const_map; rewrite !size_iota.
move=> _ [ [// | n]].
by rewrite /mkseq /= => [[]] /eqP; rewrite eq_sym anb.
Qed.

Lemma remove_headP2 (T : eqType) (a : T) s :
  exists n, s = mkseq (fun _ => a) n ++ remove_head a s.
Proof.
elim: s => [ | b tl [n Ih]] /=.
  by exists 0%N.
case: ifP => [/eqP <- | anb].
  exists n.+1=> /=; rewrite [in LHS]Ih /=.
  by congr (_ :: _ ++ _); apply: const_map; rewrite !size_iota.
by exists 0%N.
Qed.

Lemma size_remove_head (T : eqType) (a : T) s :
   (size (remove_head a s) <= size s)%N.
Proof.
have [n Pn] := remove_headP2 a s.
by rewrite [X in (_ <= size X)%N]Pn size_cat size_map size_iota leq_addl.
Qed.

Lemma remove_head_mkseq (T : eqType) (a : T) n l :
  remove_head a (mkseq (fun=> a) n ++ l) = remove_head a l.
Proof.
elim: n => //= n Ih; rewrite eqxx -Ih; congr (_ _ (_ ++ _)); apply: const_map.
by rewrite !size_iota.
Qed.

Fixpoint unstutter (T : eqType) (s : seq T) : seq T :=
  if s is a :: tl then a :: unstutter (remove_head a tl) else s.

Lemma unstutter0 (T : eqType) (s : seq T) :
  (unstutter s == [::]) = (s == [::]).
Proof.  by case: s. Qed.

Lemma cons_mkseq (T : eqType) (a : T) n :
  a :: mkseq (fun=> a) n = rcons (mkseq (fun=> a) n) a.
Proof.
elim: n => [ | n Ih] //=; rewrite /mkseq /=.
rewrite [X in a :: a :: X = a :: rcons X _](_ : _ = mkseq (fun=> a) n).
  by congr (_ :: _).
by rewrite /mkseq; apply: const_map; rewrite !size_iota.
Qed.

Lemma unstutter1P (T : eqType) (s : seq T) a :
  reflect (exists n, s = mkseq (fun=> a) n.+1) (unstutter s == [:: a]).
Proof.
have [it | notit] := boolP(_ == _).
  apply: ReflectT.
  elim: s it => [// | a' s Ih] /eqP /= [] -> /eqP.
  rewrite unstutter0=> /remove_head0P [n ->]; exists n.
  by rewrite /mkseq /=; congr (_ :: _); apply: const_map; rewrite !size_iota.
apply: ReflectF.
elim: s notit=> [_ [n //] | a' s Ih].
move/eqP=> abs [n]; rewrite /mkseq /= => [[]] a'a sseq; case: abs.
rewrite a'a /=; congr (_ :: _).
have /eqP -> // : remove_head a s == [::].
apply/remove_head0P.
by exists n; rewrite sseq; apply: const_map; rewrite !size_iota.
Qed.

Lemma size_unstutter (T : eqType) (s : seq T) :
  (size (unstutter s) <= size s)%N.
Proof.
move: {2} (size s) (leqnn (size s))=> sz; elim: sz s => [ | n Ih] s.
  by rewrite leqn0 size_eq0=> /eqP ->.
case: s=> [// | a s] /=; rewrite ltnS=> slen.
have /Ih sur : (size (remove_head a s) <= n)%N.
  apply: leq_trans slen; apply: size_remove_head.
by rewrite (leq_ltn_trans sur) // ltnS; apply: size_remove_head.
Qed.

Lemma unstutterPi (T : eqType) (s : seq T) (def : T) (i : nat) :
  (i < (size (unstutter s)).-1)%N ->
  exists k,
     (k < (size s).-1)%N /\
     nth def (unstutter s) i = nth def s k /\
     nth def (unstutter s) i.+1 = nth def s k.+1 /\
     nth def (unstutter s) i <> nth def (unstutter s) i.+1.
Proof.
move: {2} (size s) (leqnn (size s))=> sz.
elim: sz s i => [ | sz Ih] s i.
  by rewrite leqn0 size_eq0=>/eqP ->.
case: s => [// | a s] /=; rewrite ltnS=> sizele ci.
have [n Pn] := remove_headP2 a s.
have smk : size (mkseq (fun=>a) n) = n.
  by rewrite size_map size_iota.
case: i ci => [ | i] ci.
  case rhq : (remove_head a s) => [ | b tl]; first by rewrite rhq in ci.
  move/remove_headP: (rhq)=> anb.
  exists n.
  split.
    by rewrite Pn size_cat smk -[X in (X <= _)%N]addn1 leq_add2l rhq.
  split.
    rewrite /= Pn rhq -cat_cons cons_mkseq nth_cat size_rcons smk.
    by rewrite ltnSn nth_rcons smk ltnn eqxx.
  split.
    by rewrite /= Pn rhq nth_cat smk ltnn subnn.
  by rewrite /=; apply/eqP.
move: ci; rewrite -ltn_predRL=> ci.
have srh : (size (remove_head a s) <= sz)%N.
  by apply: leq_trans sizele; apply: size_remove_head.
have [k [Pk1 [Pk2 [Pk3 Pk4]]]] := Ih _ _ srh ci.
exists (n + k).+1=>/=.
split.
  move: (Pk1); rewrite ltn_predRL=>/ltn_predK sizeps.
  by rewrite Pn size_cat smk -2!addnS -sizeps leq_add2l ltnS.
split.
  by rewrite Pk2 [in RHS]Pn nth_cat smk ltnNge leq_addr /= addKn.
split=> //.
by rewrite Pk3 [in RHS] Pn nth_cat smk ltnNge -addnS leq_addr addKn.
Qed.

Lemma unstutter_Pi' (T : eqType) (s : seq T) (def : T) i :
  (i < (size s).-1)%N ->
  nth def s i <> nth def s i.+1 ->
  exists k, (k < (size (unstutter s)).-1)%N /\
    nth def (unstutter s) k = nth def s i /\
    nth def (unstutter s) k.+1 = nth def s i.+1.
Proof.
move: {2} (size s) (leqnn (size s))=> sz; elim: sz s i=> [ | n Ih] s i.
  by rewrite leqn0 size_eq0=> /eqP ->.
case: s=> [// | c s] /=.
rewrite ltnS => slen.
case: i=> /= [ | i].
  case rhv: (remove_head c s) => [ | b tl] /=.
    case: s slen rhv => [ | b tl] slen /= rhv //= _ cnb.
    by move/eqP: cnb=> cnb; rewrite (negbTE cnb) in rhv.
  move=> sizes fsts.
  exists 0%N => /=; split;[ by [] | split;[by [] | ] ].
  case: s rhv sizes fsts {slen}=> /= [// | b' tl'] rhv sizes /eqP fsts.
  by rewrite (negbTE fsts) in rhv; move: rhv=> [] ->.
case: s slen => [// | b s] /= slen.
rewrite ltnS.
move=> isize idiff.
have [k [/= Pk1 [Pk2 Pk3]]] := Ih (b :: s) i slen isize idiff.
have [/eqP -> | cneqb] := boolP(c == b).
  by exists k.
by exists k.+1.
Qed.

Lemma unstutterP1 (T : eqType) (s l1 l2 : seq T) a b :
  unstutter s = l1 ++ a :: b :: l2 -> a != b.
Proof.
move=> cnd.
have /(unstutterPi a) [k [_ [_ [_ ]]]]: (size l1 < (size (unstutter s)).-1)%N.
  by rewrite cnd size_cat /= !addnS /= ltnS leq_addr.
by rewrite cnd !nth_cat ltnn subnn /= ltnNge leqnSn subSnn /= =>/eqP.
Qed.

Lemma unstutter_is_seq1 (T : eqType) (a : T) l :
  unstutter l = [:: a] -> exists n, l = mkseq (fun => a) n.
Proof.
elim: l => [ | a' [ | b l] Ih] // [] -> {a'}.
  by exists 1%N.
rewrite [X in X = _ -> _](_ :_ = unstutter (remove_head a (b :: l)));
   last by [].
case rh : (remove_head a (b :: l)) => [ | a' l'] //.
move/eqP/remove_head0P: rh=> [n ->] _; exists n.+1; rewrite /mkseq /=.
by congr (_ :: _); apply: const_map; rewrite !size_iota.
Qed.

Lemma unstutter_is_cons (T : eqType) (s l1 : seq T) a :
  unstutter s = a :: l1 ->
  exists n l2, s = a :: mkseq (fun=> a) n ++ l2 /\
   l1 = unstutter l2.
Proof.
case: s => [ | c s] //= [] -> {c} uns.
have [n Pn] := remove_headP2 a s.
exists n; exists (remove_head a s); split; last by [].
by rewrite -Pn.
Qed.

Lemma unstutterP2 (T : eqType) (s l1 l2 : seq T) a b :
  unstutter s = l1 ++ a :: b :: l2 -> exists l3 l4, s = l3 ++ a :: b :: l4.
Proof.
move=> unstq.
set i := size l1.
have ilt : (i < (size (unstutter s)).-1)%N.
  by rewrite unstq size_cat /= 2!addnS ltnS leq_addr.
have [k [Pk1 [Pk2 [Pk3 Pk4]]]]:= unstutterPi a ilt.
exists (take k s); exists (drop k.+2 s).
  rewrite -[LHS](cat_take_drop k); congr (_ ++ _).
rewrite (drop_nth a); last first.
  by apply/(leq_trans Pk1)/leq_pred.
congr (_ :: _).
  by rewrite -Pk2 unstq nth_cat ltnn subnn.
rewrite (drop_nth a); last by rewrite -ltn_predRL.
congr (_ :: _); rewrite -Pk3 unstq nth_cat.
by rewrite ltnNge leqnSn /= -/i -addn1 addKn.
Qed.

Definition beachline_sites (pts : seq (R ^ 2)) (swp : R) :=
  unstutter (pre_beachline_sites pts swp).

Lemma roots_exclude_i (p : {poly R})(i : nat) x :
  (i < (size (rootsR p)).-1)%N ->
  (rootsR p)`_i < x < (rootsR p)`_i.+1 -> ~root p x.
Proof.
rewrite /rootsR.
elim: i (cauchy_bound p) (- cauchy_bound p) => [ | i Ih] d c;
  case rq: (roots p c d) => [// | a tl] /=; move/eqP: rq.
  case: tl => [ // | b tl].
  rewrite roots_cons=> /andP[] pn0 /andP[] _ /andP[] _ /andP[] _ rpad _ axb.
  move: rpad; rewrite roots_cons=> /andP[] _ /andP[] _ /andP[] /eqP rpab _.
  by move/roots_nil: rpab=> /(_ pn0)=> it; apply /negP/it.
rewrite roots_cons=> /andP[] pn0 /andP[] _ /andP[] _ /andP[] _ /eqP <-.
by rewrite -ltn_predRL; apply: Ih.
Qed.

Definition pdiff p1 p2 swp : {poly R} :=
  parabola (p_x p1) (p_y p1) swp -
  parabola (p_x p2) (p_y p2) swp.

Lemma parabola_interval (p1 p2 : R ^ 2) swp (a b c : R) :
  {in `]a, b[, forall x, ~~root (pdiff p1 p2 swp) x} ->
  c \in `]a, b[ ->
  parabola' p2 swp c < parabola' p1 swp c ->
  {in `]a, b[, forall x, parabola' p2 swp x < parabola' p1 swp x}.
Proof.
move=> noroot /andP[altc cltb].
rewrite -subr_gt0 /parabola' -hornerN -hornerD -/(pdiff p1 p2 swp)=> diffgt0.
move=> x xin.
rewrite -subr_gt0 /parabola' -hornerN -hornerD -/(pdiff p1 p2 swp).
rewrite ltNge le_eqVlt; apply/negP=> /orP [xroot | xopp].
  by move: (noroot x xin); rewrite /root xroot.
have [ | xgtseq] := boolP(x <= c).
  rewrite le_eqVlt=> /orP[/eqP xeqc | xltc].  
    by move: xopp; rewrite xeqc ltNge le_eqVlt diffgt0 orbT.
  have /(@poly_ivt _ (pdiff p1 p2 swp)) : x <= c by rewrite ltW.
  rewrite ltW // ltW // => /(_ isT) [r /andP [xler rlec] rroot].
  have xin' : a < r < b.
    move/andP: xin => [] altx xltb.
    by rewrite (lt_le_trans _ xler) // (le_lt_trans rlec) //.
  by move: (noroot r xin'); rewrite rroot.
have /(@poly_ivt _ (-(pdiff p1 p2 swp))) : c <= x by rewrite ltW // ltNge.
rewrite 2!hornerN oppr_le0 ltW // oppr_ge0 ltW //.
move => /(_ isT) [r /andP [cler rlex] rroot].
have xin' : a < r < b.
  move/andP: xin => [] altx xltb.
  by rewrite (lt_le_trans _ cler) // (le_lt_trans rlex) //.
move: rroot; rewrite rootN=> rroot.
by move: (noroot r xin'); rewrite rroot.
Qed.

Lemma same_x_parabola_cmp (p1 p2 : R ^ 2) swp :
  p_x p1 < swp ->
  p_x p1 = p_x p2 -> p_y p1 < p_y p2 ->
  (forall y, y < (p_y p1 + p_y p2)/2%:R -> 
     parabola' p2 swp y < parabola' p1 swp y) /\
  (forall y, (p_y p1 + p_y p2)/2%:R < y -> 
     parabola' p1 swp y < parabola' p2 swp y).
Proof.
move=> p1lts p1p2 p1ltp2.
set w:=  ((p_y p2 - p_y p1) / (swp - p_x p2))%:P * 
         (((p_y p2 + p_y p1) / 2%:R)%:P - 'X).
have reorg : forall x, parabola' p1 swp x - parabola' p2 swp x = w.[x].
  move=> x; rewrite /parabola' -hornerN -hornerD parabola_diff_reorg.
  rewrite /parabola2 p1p2 subrr mul0r addr0.
  rewrite /parabola0 p1p2 opprD addrA opprK (addrAC (_ / 2%:R)) addrN sub0r.
  rewrite (addrC (- _)) -mulrBl subr_sqr invfM mulrA (mulrC (_ - _)).
  rewrite (mulrAC (_ + _)) -(mulrA (_ / 2%:R)) polyCM.
  rewrite addrC /parabola1 p1p2 -mulrBl -opprB mulNr polyCN mulNr addrC.
  by rewrite -(mulrC 'X) -mulrBl mulrC.
have factorp : 0 < (p_y p2 - p_y p1) / (swp - p_x p2).
  by apply: divr_gt0; rewrite subr_gt0 -?p1p2.
split=> y wherey; [rewrite -subr_gt0 reorg | rewrite -subr_lt0 reorg].
  by rewrite !hornerE mulr_gt0 // subr_gt0 addrC.
by rewrite !hornerE pmulr_rlt0 // subr_lt0 addrC.
Qed.

Lemma parabola_connect (p1 p2 : R ^ 2) swp (a b c d e : R) :
  p_x p1 < swp -> p_x p2 < swp ->
  {in `]a, b[, forall x, ~~root (pdiff p1 p2 swp) x} ->
  {in `]b, c[, forall x, ~~root (pdiff p1 p2 swp) x} ->
  d \in `]a, b[ -> parabola' p2 swp d < parabola' p1 swp d ->
  e \in `]b, c[ -> parabola' p2 swp e < parabola' p1 swp e ->
  {in `]a, c[, forall x, parabola' p2 swp x < parabola' p1 swp x}.
Proof.
move=> p1lts p2lts norootleft norootright dleft dP eright eP.
have xlt : forall x, x \in `]a, b[ -> parabola' p2 swp x < parabola' p1 swp x.
  by move=> x xin; apply: (parabola_interval norootleft (_ : d \in `]a, b[)).
have xgt : forall x, x \in `]b, c[ -> parabola' p2 swp x < parabola' p1 swp x.
  by move=> x xin; apply: (parabola_interval norootright (_ : e \in `]b,c[)).
move=> x /andP[] altx xltc.
have[xltb | ]:= boolP(x < b).
  by apply/xlt/andP.
rewrite -leNgt le_eqVlt=>/orP[/eqP xisb | cltx]; last first.
  by apply/xgt/andP.
have [/eqP p1p2x | p1np2x] := boolP (p_x p1 == p_x p2).
  have [p1ltp2 | ] := boolP(p_y p1 < p_y p2).
    have [abs1 abs2]:= same_x_parabola_cmp p1lts p1p2x p1ltp2.
    apply: abs1; rewrite -xisb (@lt_le_trans _ _ e) //.
      by case/andP: eright.
    by rewrite leNgt; apply/negP=> /abs2; rewrite ltNge le_eqVlt eP orbT.
  rewrite -leNgt le_eqVlt=> /orP[/eqP p1p2y| p2ltp1 ]; last first.
    have [abs1 abs2]:= same_x_parabola_cmp p2lts (esym p1p2x) p2ltp1.
    apply: abs2; rewrite -xisb (@le_lt_trans _ _ d) //; last first.
      by case/andP: dleft.
    by rewrite leNgt; apply/negP=> /abs1; rewrite ltNge le_eqVlt dP orbT.
  have p1p2 : p1 = p2 by apply/pt_eqP; rewrite p1p2x p1p2y !eqxx.
  by move:eP; rewrite p1p2 ltxx.
have [ p1ltp2x | ] := boolP(p_x p1 < p_x p2).
  rewrite -subr_gt0 /parabola' -hornerN -hornerD parabola_diff_reorg.
  set w0 := (X in ((X)%:P + _ + _)); set w1 := (X in (_ + (X)%:P * _ + _)).
  set w2 := (X in (_ + _ + (X)%:P * _)).
  have lead_coef_lt : 0 < w2.
    rewrite subr_gt0 /parabola2 ltr_oppr opprK.
    rewrite ltf_pinv // ?posrE ?mulr_gt0 // ?ltr0Sn // ?subr_gt0 //.
    by rewrite ltr_pmul2l ?ltr0Sn // ltr_add2l ltr_oppr opprK.
  have negv : exists x, (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[x] < 0.
    exists (p_y p2); rewrite -parabola_diff_reorg hornerD hornerN subr_lt0.
    by apply: parabola_diff_min; rewrite p1ltp2x p2lts.
  have [r1 [r2 [r1ltr2 [r1root [r2root [posvals [negvals _]]]]]]] :=
   solve_snd_degreep lead_coef_lt negv.
  have dP' : 0 < (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[d].
    by rewrite -parabola_diff_reorg hornerD hornerN subr_gt0.
  have eP' : 0 < (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[e].
    by rewrite -parabola_diff_reorg hornerD hornerN subr_gt0.
  have common_x_le u :
       r1 <= u <= r2 -> (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[u] <= 0.
    rewrite 2!le_eqVlt=> /andP[] /orP[/eqP <- | r1ltu /orP [/eqP -> | ultr2]].
        by rewrite r1root.
      by rewrite r2root.
    by rewrite le_eqVlt orbC negvals // r1ltu ultr2.
  have dout : (d < r1) || (r2 < d).
    rewrite 2!ltNge -negb_and; apply/negP=> /common_x_le.
    by rewrite leNgt dP'.
  have eout : (e < r1) || (r2 < e).
    rewrite 2!ltNge -negb_and; apply/negP=> /common_x_le.
    by rewrite leNgt eP'.
  suff hard : r2 < e -> d < r1 -> 0 < (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[x].
    case/orP:dout.
      case/orP:eout.
        move=> eltr1 _; apply: posvals; left; apply: lt_trans eltr1.
        by rewrite -xisb; case/andP: eright.
      exact: hard.    
    move=> r2ltd; apply: posvals; right; apply: (lt_trans r2ltd).
    by rewrite -xisb; case/andP: dleft.
  move=> r2lte dltr1 {dout eout}; rewrite -xisb.
  have [bltr1 | ] := boolP(b < r1).
    have r1right : b < r1 < c.
      by rewrite bltr1 (lt_trans r1ltr2) // (lt_trans r2lte); case/andP:eright.
    have := norootright r1 r1right.
    by rewrite /root /pdiff parabola_diff_reorg r1root eqxx.
  rewrite -leNgt le_eqVlt => /orP[/eqP r1isb | r1ltb].
  have r2right : b < r2 < c.
    by rewrite -r1isb r1ltr2 (lt_trans r2lte) //; case/andP: eright.
    have := norootright r2 r2right.
    by rewrite /root /pdiff parabola_diff_reorg r2root eqxx.
  have r1left : a < r1 < b.
    by rewrite r1ltb andbT (lt_trans _ dltr1) //; case/andP: dleft.
  have := norootleft r1 r1left.
  by rewrite /root /pdiff parabola_diff_reorg r1root eqxx.

rewrite -leNgt le_eqVlt eq_sym (negbTE p1np2x) /=.
move=> p2ltp1x.
rewrite -subr_lt0 /parabola' -hornerN -hornerD parabola_diff_reorg.
set w0 := (X in ((X)%:P + _ + _)); set w1 := (X in (_ + (X)%:P * _ + _)).
set w2 := (X in (_ + _ + (X)%:P * _)).
have lead_coef_lt : 0 < w2.
  rewrite subr_gt0 /parabola2 ltr_oppr opprK.
  rewrite ltf_pinv // ?posrE ?mulr_gt0 // ?ltr0Sn // ?subr_gt0 //.
  by rewrite ltr_pmul2l ?ltr0Sn // ltr_add2l ltr_oppr opprK.
have negv : exists x, (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[x] < 0.
  exists (p_y p1); rewrite -parabola_diff_reorg hornerD hornerN subr_lt0.
  by apply: parabola_diff_min; rewrite p2ltp1x p1lts.
have [r1 [r2 [r1ltr2 [r1root [r2root [posvals [negvals _]]]]]]] :=
   solve_snd_degreep lead_coef_lt negv.
have dP' : (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[d] < 0.
  by rewrite -parabola_diff_reorg hornerD hornerN subr_lt0.
have eP' : (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[e] < 0.
  by rewrite -parabola_diff_reorg hornerD hornerN subr_lt0.
have common_x_le u :
       (u <= r1) || (r2 <= u) -> 0 <= (w0%:P + w1%:P * 'X + w2%:P * 'X^2).[u].
  rewrite 2!le_eqVlt => /orP[/orP [/eqP -> | ultr1] | /orP[/eqP <- | r2ltu] ].
        by rewrite r1root.
      by rewrite le_eqVlt orbC posvals //; left.
    by rewrite r2root.
  by rewrite le_eqVlt orbC posvals //; right.
have /andP[r1ltd dltr2] : r1 < d < r2.
  rewrite 2!ltNge -negb_or; apply/negP=> /common_x_le.
  by rewrite leNgt dP'.
have /andP[r1lte eltr2] : r1 < e < r2.
  rewrite 2!ltNge -negb_or; apply/negP=> /common_x_le.
  by rewrite leNgt eP'.
rewrite -xisb.
have /negvals // : r1 < b < r2.
rewrite (lt_trans r1ltd) ?(lt_trans _ eltr2) //.
  by case/andP: eright.
by case/andP: dleft.
Qed.

