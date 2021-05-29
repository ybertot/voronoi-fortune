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

Lemma no_roots_constant_sign (p : {poly R}) (a b c : R) :
  c \in `]a, b[ ->
  (forall x, x \in `]a, b[ -> ~~ root p x) ->
  forall x, a <= x <= b -> 0 <= Num.sg p.[x] * Num.sg p.[c].
Proof.
move=> cinab.
have alec : a <= c.
  by rewrite ltW //; move/andP:cinab => [].
have cleb : c <= b.
  by rewrite ltW //; move/andP:cinab => [].
have aleb : a <= b by apply: le_trans cleb.
move=> noroots.
have sgc : (Num.sg p.[c] == -1) || (Num.sg p.[c] == 1).
  rewrite /Num.sg; case: ifP.
    by move/eqP=> pc0; move: (noroots c cinab); rewrite /root pc0 eqxx.
  by move/negbT=> pcn0; case: ifP; rewrite eqxx ?orbT.
move=> x /andP[] alex xleb.
have sgx : (Num.sg p.[x] == -1) || (Num.sg p.[x] == 1)
      || (Num.sg p.[x] == 0).
  rewrite /Num.sg; case: ifP; rewrite ?eqxx ?orbT //.
  by case: ifP; rewrite ?eqxx ?orbT.
have [xlec | ] := boolP(x <= c).
  move/orP: sgc=>[] /eqP sgc.
    move/orP: sgx=>[/orP [] | ] /eqP sgx;
      rewrite sgx sgc ?mulNr ?mulrN ?opprK ?mulr1 ?mul0r ?lexx ?ler01 //.
      have/(ivt_sign xlec) [r Pr1 Pr2] : Num.sg p.[x] * Num.sg p.[c] = -1.
        by rewrite sgc sgx mulrN mul1r.
      move: (noroots r); rewrite Pr2=> nor'.
      have/nor' // : r \in `]a, b[.
      apply/andP; split; first by apply: (le_lt_trans alex); case/andP: Pr1.
      by apply: lt_le_trans cleb; case/andP: Pr1.
    by rewrite oppr0 lexx.
  move/orP: sgx=>[/orP [] | ] /eqP sgx;
    rewrite sgx sgc ?mulNr ?mulrN ?opprK ?mulr1 ?mul0r ?lexx ?ler01 //.
  have/(ivt_sign xlec) [r Pr1 Pr2] : Num.sg p.[x] * Num.sg p.[c] = -1.
    by rewrite sgc sgx mulNr mul1r.
  move: (noroots r); rewrite Pr2=> nor'.
  have/nor' // : r \in `]a, b[.
  apply/andP; split; first by apply: (le_lt_trans alex); case/andP: Pr1.
  by apply: lt_le_trans cleb; case/andP: Pr1.
rewrite -ltNge=> cltx; have clex := ltW cltx; rewrite mulrC.
move/orP: sgc=>[] /eqP sgc.
  move/orP: sgx=>[/orP [] | ] /eqP sgx;
    rewrite sgx sgc ?mulNr ?mulrN ?opprK ?mulr1 ?mul1r ?mul0r ?lexx ?ler01 //.
    have/(ivt_sign clex) [r Pr1 Pr2] : Num.sg p.[c] * Num.sg p.[x] = -1.
      by rewrite sgc sgx mulNr mul1r.
    move: (noroots r); rewrite Pr2=> nor'.
    have/nor' // : r \in `]a, b[.
    apply/andP; split; last by apply: (lt_le_trans _ xleb); case/andP: Pr1.
    by apply: (le_lt_trans alec); case/andP: Pr1.
  by rewrite oppr0 lexx.
move/orP: sgx=>[/orP [] | ] /eqP sgx;
  rewrite sgx sgc ?mulNr ?mulrN ?opprK ?mulr1 ?mulr0 ?lexx ?ler01 //.
have/(ivt_sign clex) [r Pr1 Pr2] : Num.sg p.[c] * Num.sg p.[x] = -1.
  by rewrite sgc sgx mulrN mulr1.
move: (noroots r); rewrite Pr2=> nor'.
have/nor' // : r \in `]a, b[.
apply/andP; split; last by apply: (lt_le_trans _ xleb); case/andP: Pr1.
by apply: (le_lt_trans alec); case/andP: Pr1.
Qed.

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

Lemma sqrt_ivt_step1  (p1 p2 p3 : {poly R}) (a b : R):
   (forall x, a <= x <= b -> 0 <= p1.[x]) ->
   (forall x, a <= x <= b -> 0 <= p3.[x]) ->
   a <= b -> p1.[a] + p2.[a] * Num.sqrt p3.[a] <= 0 <=
             p1.[b] + p2.[b] * Num.sqrt p3.[b] ->
   exists2 x, a <= x <= b &
       p1.[x] + p2.[x] * Num.sqrt p3.[x] = 0.
Proof.
move=> p1ge0 p3ge0 aleb sign_condition.
case: (rootsP p2 a b) (path_roots p2 a b).
  move=> p20 _ _; move: sign_condition; rewrite p20 !horner0 !mul0r !addr0.
    move=> /(poly_ivt aleb) [r Pr1 Pr2].
    by exists r; rewrite // horner0 mul0r addr0; apply/eqP.
move: (roots p2 a b)=> s; move: s a b p1ge0 p3ge0 aleb sign_condition.
elim => [ | r rts Ih] a b p1ge0 p3ge0 aleb sign_condition.
  move=> p2n0 /roots_on_nil noroots _ _.
  have [/eqP p2ais0 | p2an0] := boolP(p2.[a] == 0).
    exists a; first by rewrite lexx aleb.
    move/andP: sign_condition => [sc1 sc2].
    by apply: le_anti; rewrite sc1 /= p2ais0 mul0r addr0 p1ge0 // lexx.
  move: aleb; rewrite le_eqVlt=> /orP[/eqP aisb | altb].
    exists a; first by rewrite lexx le_eqVlt aisb eqxx.
    by apply: le_anti; move: sign_condition; rewrite aisb.
  set c := (a + b) / 2%:R.
  have altc : a < c.
    by rewrite /c ltr_pdivl_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2l.
  have cltb : c < b.
    by rewrite /c ltr_pdivr_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2r.
  have /noroots : c \in `]a, b[ by apply/andP.
  rewrite /root=> p2cn0. 
  have [ | ] := boolP(0 <= p2.[c]).
    rewrite le_eqVlt eq_sym (negbTE p2cn0) /= => p2cgt0.
    have sgp2c : 0 < Num.sg (p2.[c]) by rewrite sgr_gt0.
    have cinab : c \in `]a,b[ by apply/andP.
    have p2agt0 : 0 < p2.[a].
      rewrite lt_neqAle eq_sym p2an0 /= -sgr_ge0 -(pmulr_lge0 _ sgp2c).
      apply: (no_roots_constant_sign cinab noroots).
      by rewrite lexx ltW.
    exists a; first by rewrite lexx ltW.
    apply: le_anti; move/andP: sign_condition=> [] -> _ /=.
    rewrite addr_ge0 //; first by rewrite p1ge0 // lexx (ltW altb).
    by rewrite pmulr_rge0 // sqrtr_ge0.
  rewrite -ltNge=> p2clt0.
  have cinab : c \in `]a, b[ by apply/andP; split.
  have sgp2 := no_roots_constant_sign cinab noroots.
  have sgp2c : Num.sg p2.[c] < 0 by rewrite sgr_lt0.
  have p2le0 : forall x, a <= x <= b -> p2.[x] <= 0.
    by move=> x /sgp2 intx; rewrite -sgr_le0 -(nmulr_lge0 _ sgp2c).
  by apply: sqrt_ivt_base=> //; rewrite ltW.
move=> p2n0 rson sseq pseq.
have altr : a < r by move: pseq; rewrite /= => /andP[].
have rltb : r < b.
  by move/roots_on_in: rson=> /(_ r); rewrite inE eqxx=> /(_ isT)/andP[].
have rleb := ltW rltb.
have [pneg | ] := boolP (p1.[r] + p2.[r] * Num.sqrt p3.[r] < 0).
  suff [r' /andP[rler' r'leb] Pr2]:
       exists2 x, r <= x <= b & p1.[x] + p2.[x] * Num.sqrt p3.[x] = 0.
    exists r'; last by []. 
    rewrite r'leb (le_trans _ rler') //.
    by move: pseq; rewrite /= => /andP[] /ltW.
  have p1ge' : forall x, r <= x <= b -> 0 <= p1.[x].
    move=> x /andP[] rlex xleb; apply p1ge0.
    by  rewrite xleb (ltW (lt_le_trans _ rlex)).
  have p3ge' : forall x, r <= x <= b -> 0 <= p3.[x].
    move=> x /andP[] rlex xleb; apply p3ge0.
    by  rewrite xleb (ltW (lt_le_trans _ rlex)).
  have signrb : p1.[r] + p2.[r] * Num.sqrt p3.[r] <= 0
            <= p1.[b] + p2.[b] * Num.sqrt p3.[b].
    by rewrite ltW ?pneg //; move/andP: sign_condition=>[].
  have rootsrb : roots_on p2 `]r, b[ rts.
    by move/roots_on_cons: rson=> /(_ sseq).
  apply: Ih=> //. 
  by move: pseq=> /=/andP[] _ /path_sorted.
rewrite -leNgt=> prge0.
have noroots : {in `]a, r[, forall x, ~~root p2 x}.
  move=> x xinar; move: (xinar)=> /andP[] altx xltr; apply/negP=> abs.
  have xinab : x \in `]a, b[.
    by apply/andP; split=> //; apply: (lt_le_trans xltr).
  move: (pseq); rewrite /= => /andP[] _.
  rewrite (path_sortedE lt_trans r rts)=> /andP[] allgt _.
  move: (root_roots_on rson xinab abs); rewrite inE=> /orP[/eqP xisr | ].
    have : x < r by exact: xltr.
    by rewrite xisr ltxx.
  by move/(allP allgt); rewrite ltNge le_eqVlt orbC; have -> : x < r.
suff [r' /andP[aler' r'ler] Pr2]:
  exists2 x, a <= x <= r & p1.[x] + p2.[x] * Num.sqrt p3.[x] = 0.
  by exists r'; first rewrite aler' (le_trans r'ler rleb).
set c := (a + r) / 2%:R.
have altc : a < c.
  by rewrite /c ltr_pdivl_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2l.
have cltr : c < r.
  by rewrite /c ltr_pdivr_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2r.
have cinar : c \in `]a, r[ by apply/andP.
have /noroots p2cn0 := cinar.
have signs := no_roots_constant_sign cinar noroots.
have [p2clt0 | ] := boolP (p2.[c] < 0).
  have p2le0' : forall x, a <= x <= r -> p2.[x] <= 0.
    move=> x intx; have := signs _ intx.
    by rewrite nmulr_lge0 ?sgr_le0 // sgr_lt0.
  have p1ge0' : forall x, a <= x <= r -> 0 <= p1.[x].
    by move=> x /andP[] alex xler; apply p1ge0; rewrite alex (le_trans xler).
  have p3ge0' : forall x, a <= x <= r -> 0 <= p3.[x].
    by move=> x /andP[] alex xler; apply p3ge0; rewrite alex (le_trans xler).
  apply: sqrt_ivt_base=> //. 
    by apply: ltW.
  by move: sign_condition=> /andP[] -> _.
rewrite -leNgt le_eqVlt eq_sym; move: p2cn0; rewrite /root=> /negbTE -> /=. 
rewrite -sgr_gt0; move=> p2cgt0.
have/(_ a) := no_roots_constant_sign cinar noroots.
rewrite lexx (ltW altr)=> /(_ isT).
rewrite (pmulr_lge0 _ p2cgt0) sgr_ge0=> p2age0.
exists a; first by rewrite lexx ltW.
apply: le_anti; apply/andP; split; first by case/andP: sign_condition.
by rewrite addr_ge0 ?p1ge0 // ?lexx ?aleb // mulr_ge0 // sqrtr_ge0.
Qed.

Lemma sqrt_ivt_step1N  (p1 p2 p3 : {poly R}) (a b : R):
   (forall x, a <= x <= b -> p1.[x] <= 0) ->
   (forall x, a <= x <= b -> 0 <= p3.[x]) ->
   a <= b -> p1.[a] + p2.[a] * Num.sqrt p3.[a] <= 0 <=
             p1.[b] + p2.[b] * Num.sqrt p3.[b] ->
   exists2 x, a <= x <= b &
       p1.[x] + p2.[x] * Num.sqrt p3.[x] = 0.
Proof.
move=> p1le0 p3ge0 aleb sign_condition.
set p1' := -p1 \Po (-'X).
set p2' := -p2 \Po (-'X).
set p3' := p3 \Po (-'X).
have aleb' : -b <= -a by rewrite ler_oppr opprK.
have p1'ge0 : forall x, -b <= x <= -a -> 0 <= p1'.[x].
  move=> x /andP[]; rewrite ler_oppl ler_oppr => mxleb alemx.
  rewrite /p1' horner_comp !hornerE ler_oppr oppr0.
  by apply: p1le0; rewrite mxleb alemx.
have p3'ge0 : forall x, -b <= x <= -a -> 0 <= p3'.[x].
  move=> x /andP[]; rewrite ler_oppl ler_oppr => mxleb alemx.
  rewrite /p3' horner_comp !hornerE.
  by apply: p3ge0; rewrite mxleb alemx.
have peq x : p1.[x] + p2.[x] * Num.sqrt p3.[x] =
       -(p1'.[-x] + p2'.[-x] * Num.sqrt p3'.[-x]).
  by rewrite /p1' /p2' /p3' !horner_comp !hornerE !mulNr -!opprD !opprK.
have sign_condition' :
  p1'.[-b] + p2'.[-b] * Num.sqrt p3'.[-b] <= 0 <=
  p1'.[-a] + p2'.[-a] * Num.sqrt p3'.[-a].
  by rewrite -oppr0 ler_oppl ler_oppr -!peq andbC.
have [r Pr1 Pr2]:= sqrt_ivt_step1 p1'ge0 p3'ge0 aleb' sign_condition'.
exists (-r); first by rewrite andbC ler_oppl ler_oppr.
by rewrite peq opprK Pr2 oppr0.
Qed.

Lemma sqrt_ivt_step2 (p1 p2 p3 : {poly R})(a b : R) :
  (forall x : R, a <= x <= b -> 0 <= p3.[x]) ->
       a <= b ->
       p1.[a] + p2.[a] * Num.sqrt p3.[a] <= 0 <=
       p1.[b] + p2.[b] * Num.sqrt p3.[b] ->
       exists2 x : R, a <= x <= b & p1.[x] + p2.[x] * Num.sqrt p3.[x] = 0.
Proof.
move=> p3ge0 aleb sign_condition.
move: aleb; rewrite le_eqVlt=>/orP[/eqP aisb | altb].
  exists a; first by rewrite aisb !lexx.
  by apply: le_anti; case/andP: sign_condition; rewrite aisb => ->.
case: (rootsP p1 a b) (path_roots p1 a b).
  move=> p10 _ _.
  have/(fun h => sqrt_ivt_step1 h p3ge0 (ltW altb) sign_condition) :
    forall x, a <= x <= b -> 0 <= p1.[x].
    by move=> x _; rewrite p10 hornerE lexx.
  by rewrite p10.
move: (roots p1 a b)=> l.
elim: l a b p3ge0 sign_condition altb => [ | r rts Ih]
   a b p3ge0 sign_condition altb p1n0 rson sseq pseq.
set c := (a + b) / 2%:R.
have altc : a < c.
  by rewrite /c ltr_pdivl_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2l.
have cltr : c < b.
  by rewrite /c ltr_pdivr_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2r.
have cinab : c \in `]a, b[ by apply/andP.
have cstsg := no_roots_constant_sign cinab (roots_on_nil rson).
have [ | ] := boolP(p1.[c] < 0).
  rewrite -sgr_lt0=> p1clt0.
  have p1le0 : forall x, a <= x <= b -> p1.[x] <= 0.
    by move=> x xi; have := cstsg x xi; rewrite (nmulr_lge0 _ p1clt0) sgr_le0.
  by apply: sqrt_ivt_step1N; rewrite // ltW.
  rewrite -leNgt le_eqVlt -sgr_gt0=> /orP[abs | p1cgt0].
    by have := roots_on_nil rson cinab; rewrite /root eq_sym abs.
  have p1ge0 : forall x, a <= x <= b -> 0 <= p1.[x].
    by move=> x xi; have := cstsg x xi; rewrite (pmulr_lge0 _ p1cgt0) sgr_ge0.
  by apply: sqrt_ivt_step1; rewrite // ltW.
have rltb : r < b.
  by move/roots_on_in: rson=> /(_ r); rewrite inE eqxx=> /(_ isT)/andP[].
have [prle0 | ] := boolP(p1.[r] + p2.[r] * Num.sqrt p3.[r] <= 0).
  have altr : a < r by move: pseq; rewrite /= => /andP[].
  have p3ge0' : forall x, r <= x <= b -> 0 <= p3.[x].
    move=> x /andP[] rlex xleb; apply: p3ge0.
    by rewrite (le_trans (ltW altr) rlex) xleb.
  have srts : sorted <%R rts.
    by move:pseq; rewrite /= => /andP[] _; apply: path_sorted.
  have prts : path <%R r rts.
    by move: pseq; rewrite /= => /andP[].
  have sign_condition' : p1.[r] + p2.[r] * Num.sqrt p3.[r] <= 0 <=
     p1.[b] + p2.[b] * Num.sqrt p3.[b].
    by rewrite prle0; case/andP: sign_condition.
  have [r' /andP[rler' r'leb] Pr2] := Ih r b p3ge0' sign_condition' rltb p1n0
      (roots_on_cons sseq rson) srts prts.
  by exists r'; rewrite // r'leb (le_trans (ltW altr) rler').
rewrite -ltNge=> prgt0.
have sign_condition' : p1.[a] + p2.[a] * Num.sqrt p3.[a] <= 0 <=
                       p1.[r] + p2.[r] * Num.sqrt p3.[r].
  by rewrite (ltW prgt0) andbT; case/andP: sign_condition.
have altr : a < r by move: pseq => /andP[].
set c := (a + r) / 2%:R.
have altc : a < c.
  by  rewrite /c ltr_pdivl_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2l.
have cltr : c < r.
  by rewrite /c ltr_pdivr_mulr ?ltr0Sn // mulr_natr mulr2n ltr_add2r.
have noroots : {in `]a, r[, forall x, ~~root p1 x}.
  move=> x xinar; move: (xinar)=> /andP[] altx xltr; apply/negP=> abs.
  have xinab : x \in `]a, b[.
    by apply/andP; split=> //; apply: (lt_trans xltr rltb).
  move: (pseq); rewrite /= => /andP[] _.
  rewrite (path_sortedE lt_trans r rts)=> /andP[] allgt _.
  move: (root_roots_on rson xinab abs); rewrite inE=> /orP[/eqP xisr | ].
    have : x < r by exact: xltr.
    by rewrite xisr ltxx.
  by move/(allP allgt); rewrite ltNge le_eqVlt orbC; have -> : x < r.
have cinar : c \in `]a, r[ by apply/andP.
have signs := no_roots_constant_sign cinar noroots.
have p3ge0' : forall x, a <= x <= r -> 0 <= p3.[x].
  move=> x /andP[] alex xler; apply: p3ge0.
  by rewrite alex (le_trans xler (ltW rltb)).
suff [r' /andP [aler' r'ler] P2] :
 exists2 x, a <= x <= r & p1.[x] + p2.[x] * Num.sqrt p3.[x] = 0.
  by exists r'; rewrite // aler' (le_trans r'ler (ltW rltb)).
have [ | ] := boolP(p1.[c] < 0).
  rewrite -sgr_lt0 => p1clt0.
  have p1le0 : forall x, a <= x <= r -> p1.[x] <= 0.
    by move=> x xi; rewrite -sgr_le0 -(nmulr_lge0 _ p1clt0) signs.
  by apply: sqrt_ivt_step1N=> //; apply: ltW.
rewrite -leNgt le_eqVlt eq_sym -sgr_gt0 => /orP[abs | p1cgt0].
  by have := noroots _ cinar; rewrite /root abs.
have p1le0 : forall x, a <= x <= r -> 0 <= p1.[x].
  by move=> x xi; rewrite -sgr_ge0 -(pmulr_lge0 _ p1cgt0) signs.
by apply: sqrt_ivt_step1=> //; apply: ltW.
Qed.
