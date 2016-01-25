import Imp
open eq.ops nat bool

namespace Equiv

open Idn Idn.aexp Idn.bexp Idn.com Idn.ceval

definition aequiv (a1 a2 : aexp) := ∀st, aeval st a1 = aeval st a2
definition bequiv (b1 b2 : bexp) := ∀st, beval st b1 = beval st b2
definition cequiv (c1 c2 : com) := ∀st st', (c1 / st ⇓ st') ↔ (c2 / st ⇓ st')

-- Exercise: 2 stars (equiv_classes)
-- omit

example : aequiv (AMinus (AId X) (AId X)) (ANum 0) :=
begin
  unfold aequiv,
  intro,
  unfold aeval,
  apply !nat.sub_self
end

example : bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue :=
begin
  unfold bequiv, intro,
  unfold beval, unfold aeval,
  rewrite nat.sub_self
end

theorem skip_left: ∀c, cequiv (SKIP ;; c) c :=
begin
  unfold cequiv, intros,
  split,
    intro, cases a, cases a_1, assumption,
    intro, cases a,
      apply !E_Seq, apply !E_Skip, apply !E_Skip,
      apply !E_Seq, apply !E_Skip, apply !E_Ass, assumption,
      apply !E_Seq, apply !E_Skip, apply !E_Seq, assumption, assumption,
      apply !E_Seq, apply !E_Skip, apply (!E_IfTrue a a_1),
      apply !E_Seq, apply !E_Skip, apply (!E_IfFalse a a_1),
      apply !E_Seq, apply !E_Skip, apply (!E_WhileEnd a),
      apply !E_Seq, apply !E_Skip, apply (!E_WhileLoop a a_1 a_2)
end

-- Exercise: 2 stars (skip_right)
theorem skip_right: ∀c, cequiv (c;; SKIP) c :=
begin
  unfold cequiv, intros,
  split,
    intro, cases a, cases a_2, assumption,
    intro, cases a,
      apply (!E_Seq !E_Skip !E_Skip),
      apply (!E_Seq (!E_Ass a) !E_Skip),
      apply (!E_Seq (!E_Seq a a_1) !E_Skip),
      apply (!E_Seq (!E_IfTrue a a_1) !E_Skip),
      apply (!E_Seq (!E_IfFalse a a_1) !E_Skip),
      apply (!E_Seq (!E_WhileEnd a) !E_Skip),
      apply (!E_Seq (!E_WhileLoop a a_1 a_2) !E_Skip)
end

theorem IFB_true_simple: ∀c1 c2, cequiv (IFB BTrue THEN c1 ELSE c2 FI) c1 :=
begin
  unfold cequiv, intros,
  split,
    intro, cases a,
      assumption,
      cases a_1,
    intro, cases a,
      apply !E_IfTrue, unfold beval, apply !E_Skip,
      apply !E_IfTrue, unfold beval, apply (!E_Ass a),
      apply !E_IfTrue, unfold beval, apply (!E_Seq a a_1),
      apply !E_IfTrue, unfold beval, apply (!E_IfTrue a a_1),
      apply !E_IfTrue, unfold beval, apply (!E_IfFalse a a_1),
      apply !E_IfTrue, unfold beval, apply (!E_WhileEnd a),
      apply !E_IfTrue, unfold beval, apply (!E_WhileLoop a a_1),
      assumption
end

-- Exercise: 2 stars (IFB_false)
theorem IFB_false : ∀b c1 c2,
  bequiv b BFalse → cequiv (IFB b THEN c1 ELSE c2 FI) c2 := λb c1 c2,
assert h: ∀ st,
  (∀ st, beval st b = beval st BFalse) → beval st b = tt → false,
proof
  take st e bt,
  have p1: tt = beval st BFalse, from bt ⁻¹ ⬝ e st,
  assert p1: tt = ff, by rewrite [bt ⁻¹, e st],
  show false, by contradiction
qed,
begin
  unfold bequiv, unfold cequiv, intros,
  split,
    intro, cases a_1,
      exfalso, apply (h st a a_2),
      assumption,
    intro,
      apply (E_IfFalse),
        rewrite (a st),
        assumption
end

-- Exercise: 3 stars (swap_if_branches)
theorem swap_if_branches: ∀b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI) :=
assert h: ∀ (b1 b2 : bool), bnot b1 = b2 → b1 = bnot b2, by simp,
begin
  unfold cequiv, intros,
  split,
    intro,
      cases a,
        apply E_IfFalse,
          unfold beval, rewrite a_1, assumption,
        apply E_IfTrue,
          unfold beval, rewrite a_1, assumption,
    intro,
      cases a, unfold beval at a_1,
        apply E_IfFalse,
          apply (!h a_1), assumption,
        apply E_IfTrue,
          apply (!h a_1), assumption
end

theorem WHILE_false : ∀b c, bequiv b BFalse →
  cequiv (WHILE b DO c END) SKIP :=
assert hyp: ∀b st,
  (∀ st, beval st b = beval st BFalse) → beval st b = tt → false,
proof
  take b st e bt,
  have p1: tt = beval st BFalse, from bt ⁻¹ ⬝ e st,
  assert p1: tt = ff, by rewrite [bt ⁻¹, e st],
  show false, by contradiction
qed,
begin
  intros,
  split,
    intro, cases a_1,
      apply E_Skip,
      cases a_4, unfold bequiv at a, apply (false.elim (!hyp a a_2)),
      apply (false.elim (!hyp a a_2)),
    intro,
      cases a_1,
      apply E_WhileEnd,
        unfold bequiv at a, apply a
end

-- Exercise: 2 stars, advanced, optional (WHILE_false_informal)

lemma WHILE_true_nonterm : ∀b c st st', bequiv b BTrue →
  ¬ (WHILE b DO c END) / st ⇓ st' :=
λb c st st' be r, while_induction b c _ _ _ r (begin
   intros, unfold bequiv at be,
   rewrite (be t) at a,
   unfold beval at a,
   contradiction
  end) (λt t' t'' be2 ce we f, f)

-- Exercise: 2 stars, optional (WHILE_true_nonterm_informal)

-- Exercise: 2 stars (WHILE_true)
theorem WHILE_true: ∀b c, bequiv b BTrue →
  cequiv 
    (WHILE b DO c END)
    (WHILE BTrue DO SKIP END) :=
begin
  unfold cequiv, intros,
  split,
    intro,
      apply (false.elim (!WHILE_true_nonterm a a_1)),
    intro,
      apply (false.elim (!loop_never_stops a_1))
end

-- Exercise: 2 stars, optional (seq_assoc)
theorem seq_assoc : ∀c1 c2 c3,
  cequiv ((c1;;c2);;c3) (c1;;(c2;;c3)) :=
begin
  unfold cequiv, intros,
  split,
    intro,
      cases a, cases a_1,
      apply (!E_Seq a (!E_Seq a_3 a_2)),
    intro,
      cases a, cases a_2,
      apply (!E_Seq (!E_Seq a_1 a) a_3)
end

theorem identity_assignment : ∀ X,
  cequiv (X ::= AId X) SKIP :=
λX st st', iff.intro
(λr,
  assert st = st', begin
    cases r, apply funext, intro,
    cases decidable.em (X = x),
      rewrite (if_pos a_1), rewrite (a⁻¹), unfold aeval, rewrite a_1,
      rewrite (if_neg a_1)
  end,
  show (SKIP / st ⇓ st'), by rewrite this; exact !E_Skip)
(λr,
  assert hyp: update st' X (st' X) = st', from funext (λx, !update_same rfl),
  begin
    cases r, rewrite (eq.symm hyp) at {2},
    apply E_Ass, unfold aeval
  end)

-- Exercise: 2 stars (assign_aequiv)
theorem assign_aequiv : ∀X e,
  aequiv (AId X) e → 
  cequiv SKIP (X ::= e) :=
assert hyp: ∀X st, update st X (st X) = st, from λX st, funext (λx, !update_same rfl),
λX e ae st st', iff.intro
(λr,
  assert h1: st = st', by cases r; simp,
  suffices X ::= e / st' ⇓ update st' X (st' X), by rewrite [h1, eq.symm (hyp X st') at {2}]; assumption,
    !E_Ass (by unfold aequiv at ae; rewrite (eq.symm !ae)))
(λr,
  assert st = st', begin
    cases r, apply funext, intro,
    cases decidable.em (X = x),
      rewrite [a_1, if_pos rfl, ↑aequiv at ae, -a, -!ae, ↑aeval, a_1],
      rewrite [if_neg a_1]
    end,
  by rewrite this; apply E_Skip)

lemma refl_aequiv : ∀a, aequiv a a := by intros; simp
lemma sym_aequiv : ∀a1 a2, aequiv a1 a2 → aequiv a2 a1 := by intros; unfold aequiv at a; simp
lemma trans_aequiv : ∀a1 a2 a3, aequiv a1 a2 → aequiv a2 a3 → aequiv a1 a3 := by intros; unfold aequiv at a; unfold aequiv at a_1; simp
lemma refl_bequiv : ∀b, bequiv b b := by intros; simp
lemma sym_bequiv : ∀b1 b2, bequiv b1 b2 → bequiv b2 b1 := by intros; unfold bequiv at a; simp
lemma trans_bequiv : ∀b1 b2 b3, bequiv b1 b2 → bequiv b2 b3 → bequiv b1 b3 := by intros; unfold bequiv at a; unfold bequiv at a_1; simp
lemma refl_cequiv : ∀c, cequiv c c := by intros; simp
lemma sym_cequiv : ∀c1 c2, cequiv c1 c2 → cequiv c2 c1 := by intros; unfold cequiv at a; simp
lemma iff_trans : ∀P1 P2 P3, (P1 ↔ P2) → (P2 ↔ P3) → (P1 ↔ P3) := by simp
lemma trans_cequiv : ∀c1 c2 c3, cequiv c1 c2 → cequiv c2 c3 → cequiv c1 c3 := by intros; unfold cequiv at a; unfold cequiv at a_1; simp

theorem CAss_congruence : ∀i a1 a1', aequiv a1 a1' → cequiv (CAss i a1) (CAss i a1') := begin
  intros, split,
    intro, cases a_1, rewrite [-a_2, ↑aequiv at a, !a], apply !E_Ass, simp,
    intro, cases a_1, rewrite [-a_2, ↑aequiv at a, -!a], apply !E_Ass, simp
end

theorem CWhile_congruence : ∀b1 b1' c1 c1',
  bequiv b1 b1' → cequiv c1 c1' →
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END) :=
λb1 b1' c1 c1' be ce st st',
assert ∀b1 b1' c1 c1' st st',
  bequiv b1 b1' → cequiv c1 c1' →
  (WHILE b1 DO c1 END / st ⇓ st') →
  (WHILE b1' DO c1' END / st ⇓ st'), from λb1 b1' c1 c1' st st' be ce r,
!while_induction r
  (begin
    intros,
    rewrite [↑bequiv at be, be at a],
    apply (!E_WhileEnd a) end)
  (begin
    intros,
    rewrite [↑bequiv at be, be at a, ↑cequiv at ce, ce at a_1],
    apply (!E_WhileLoop a a_1 a_3) end),
iff.intro (λr, !this be ce r) (λr, !this (!sym_bequiv be) (!sym_cequiv ce) r)

-- Exercise: 3 stars, optional (CSeq_congruence)
theorem CSeq_congruence : ∀c1 c1' c2 c2',
  cequiv c1 c1' → cequiv c2 c2' → cequiv (c1 ;; c2) (c1' ;; c2') :=
begin
  intros, split,
    intro, cases a_2, rewrite [↑cequiv at a, a at a_3, ↑cequiv at a_1, a_1 at a_4], apply (!E_Seq a_3 a_4),
    intro, cases a_2, rewrite [↑cequiv at a, -a at a_3, ↑cequiv at a_1, -a_1 at a_4], apply (!E_Seq a_3 a_4)    
end

-- Exercise: 3 stars (CIf_congruence)
theorem CIf_congruence : ∀b b' c1 c1' c2 c2',
  bequiv b b' → cequiv c1 c1' → cequiv c2 c2' →
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI) :=
begin
  intros, split,
    intro, cases a_3,
      rewrite [↑bequiv at a, a at a_4, ↑cequiv at a_1, a_1 at a_5], apply (!E_IfTrue a_4 a_5),
      rewrite [↑bequiv at a, a at a_4, ↑cequiv at a_2, a_2 at a_5], apply (!E_IfFalse a_4 a_5),
    intro, cases a_3,
      rewrite [↑bequiv at a, -a at a_4, ↑cequiv at a_1, -a_1 at a_5], apply (!E_IfTrue a_4 a_5),
      rewrite [↑bequiv at a, -a at a_4, ↑cequiv at a_2, -a_2 at a_5], apply (!E_IfFalse a_4 a_5),
end

example:
  cequiv
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= ANum 0
     ELSE
       Y ::= ANum 42
     FI)
    (X ::= ANum 0;;
     IFB (BEq (AId X) (ANum 0))
     THEN
       Y ::= AMinus (AId X) (AId X) -- <--- changed here
     ELSE
       Y ::= ANum 42
     FI) :=
begin
  apply CSeq_congruence,
    apply refl_cequiv,
    apply CIf_congruence,
      apply refl_bequiv,
      apply CAss_congruence, unfold aequiv, intro, unfold aeval, unfold aeval, apply (eq.symm !nat.sub_self),
      apply refl_cequiv
end

definition atrans_sound (atrans : aexp → aexp) := ∀a, aequiv a (atrans a)
definition btrans_sound (btrans : bexp → bexp) := ∀b, bequiv b (btrans b)
definition ctrans_sound (ctrans : com → com) := ∀c, cequiv c (ctrans c)

definition fold_constants_aexp : aexp → aexp
| (ANum n) := ANum n
| (AId i) := AId i
| (APlus a1 a2) :=
  match (fold_constants_aexp a1, fold_constants_aexp a2) with
  | (ANum n1, ANum n2) := ANum (n1 + n2)
  | (a1',a2') := APlus a1' a2'
  end
| (AMinus a1 a2) :=
  match (fold_constants_aexp a1, fold_constants_aexp a2) with
  | (ANum n1, ANum n2) := ANum (n1 - n2)
  | (a1',a2') := AMinus a1' a2'
  end
| (AMult a1 a2) :=
  match (fold_constants_aexp a1, fold_constants_aexp a2) with
  | (ANum n1, ANum n2) := ANum (n1 * n2)
  | (a1',a2') := AMult a1' a2'
  end

example :
  fold_constants_aexp (AMult (APlus (ANum 1) (ANum 2)) (AId X)) =
  AMult (ANum 3) (AId X) := rfl

example :
  fold_constants_aexp
    (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
  = AMinus (AId X) (APlus (ANum 0) (AId Y)) := rfl

definition fold_constants_bexp : bexp → bexp
| BTrue := BTrue
| BFalse := BFalse
| (BEq a1 a2) :=
  match (fold_constants_aexp a1, fold_constants_aexp a2) with
  | (ANum n1, ANum n2) := if beq_nat n1 n2 = tt then BTrue else BFalse
  | (a1', a2') := BEq a1' a2'
  end
| (BLe a1 a2) :=
  match (fold_constants_aexp a1, fold_constants_aexp a2) with
  | (ANum n1, ANum n2) := if ble_nat n1 n2 = tt then BTrue else BFalse
  | (a1', a2') := BLe a1' a2'
  end
| (BNot b1) :=
  match fold_constants_bexp b1 with
  | BTrue := BFalse
  | BFalse := BTrue
  | b1' := BNot b1'
  end
| (BAnd b1 b2) :=
  match (fold_constants_bexp b1, fold_constants_bexp b2) with
  | (BTrue, BTrue) := BTrue
  | (BTrue, BFalse) := BFalse
  | (BFalse, BTrue) := BFalse
  | (BFalse, BFalse) := BFalse
  | (b1', b2') := BAnd b1' b2'
  end

example :
    fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
  = BTrue := rfl

example :
    fold_constants_bexp 
      (BAnd (BEq (AId X) (AId Y)) 
            (BEq (ANum 0) 
                 (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
  = BAnd (BEq (AId X) (AId Y)) BTrue := rfl

definition fold_constants_com : com → com
| SKIP := SKIP
| (i ::= a) := i ::= (fold_constants_aexp a)
| (c1 ;; c2) := (fold_constants_com c1) ;; (fold_constants_com c2)
| (IFB b THEN c1 ELSE c2 FI) :=
  match fold_constants_bexp b with
  | BTrue := fold_constants_com c1
  | BFalse := fold_constants_com c2
  | b' := IFB b' THEN fold_constants_com c1 ELSE fold_constants_com c2 FI
  end
| (WHILE b DO c END) :=
  match fold_constants_bexp b with
  | BTrue := WHILE BTrue DO SKIP END
  | BFalse := SKIP
  | b' := WHILE b' DO (fold_constants_com c) END
  end

example :
  fold_constants_com 
    (X ::= APlus (ANum 4) (ANum 5);;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
       SKIP 
     ELSE
       Y ::= ANum 0
     FI;;
     IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
       Y ::= ANum 0
     ELSE
       SKIP 
     FI;;
     WHILE BEq (AId Y) (ANum 0) DO 
       X ::= APlus (AId X) (ANum 1) 
     END) 
  =
    (X ::= ANum 9;;
     Y ::= AMinus (AId X) (ANum 3);;
     IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
       SKIP 
     ELSE
       (Y ::= ANum 0) 
     FI;;
     Y ::= ANum 0;;
     WHILE BEq (AId Y) (ANum 0) DO 
       X ::= APlus (AId X) (ANum 1) 
     END) := rfl

theorem fold_constants_aexp_sound : atrans_sound fold_constants_aexp :=
proof
  take a st,
  show aeval st a = aeval st (fold_constants_aexp a), from
    aexp.induction_on a
      (λa, rfl) (λa, rfl)
      (λa1 a2 ae1 ae2, calc
        aeval st (APlus a1 a2) = aeval st a1 + aeval st a2 : rfl
        ... = aeval st (fold_constants_aexp a1) + aeval st (fold_constants_aexp a2) : ae1 ▸ ae2 ▸ rfl
        ... = aeval st (APlus (fold_constants_aexp a1) (fold_constants_aexp a2)) : rfl
        ... = aeval st (fold_constants_aexp (APlus a1 a2)) : sorry)
      sorry sorry
qed

-- Exercise: 3 stars, optional (fold_bexp_Eq_informal)
theorem fold_constants_bexp_sound: 
  btrans_sound fold_constants_bexp := sorry

-- Exercise: 3 stars (fold_constants_com_sound)
theorem fold_constants_com_sound : 
  ctrans_sound fold_constants_com := sorry

-- Exercise: 4 stars, advanced, optional (optimize_0plus)
definition optimize_0plus : aexp → aexp
| (ANum n) := ANum n
| (AId i) := AId i
| (APlus (ANum 0) e2) := optimize_0plus e2
| (APlus e1 e2) := APlus (optimize_0plus e1) (optimize_0plus e2)
| (AMinus e1 e2) := AMinus (optimize_0plus e1) (optimize_0plus e2)
| (AMult e1 e2) := AMult (optimize_0plus e1) (optimize_0plus e2)

definition subst_aexp (i : ident) (u : aexp) : aexp → aexp
| (ANum n) := ANum n
| (AId i') := if i = i' then u else AId i'
| (APlus a1 a2) := APlus (subst_aexp a1) (subst_aexp a2)
| (AMinus a1 a2) := AMinus (subst_aexp a1) (subst_aexp a2)
| (AMult a1 a2) := AMult (subst_aexp a1) (subst_aexp a2)

example :
  subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) =
  (APlus (AId Y) (APlus (ANum 42) (ANum 53))) := rfl

definition subst_equiv_property := ∀i1 i2 a1 a2,
  cequiv (i1 ::= a1;; i2 ::= a2)
         (i1 ::= a1;; i2 ::= subst_aexp i1 a1 a2)

theorem subst_inequiv : 
  ¬ subst_equiv_property :=
proof
  take contra,
  let c1 := X ::= APlus (AId X) (ANum 1);; Y ::= AId X in
  let c2 := X ::= APlus (AId X) (ANum 1);; Y ::= APlus (AId X) (ANum 1) in
  assert c12: cequiv c1 c2, by apply contra,

  let st1 := update (update empty_state X 1) Y 1 in
  let st2 := update (update empty_state X 1) Y 2 in
  assert H1: c1 / empty_state ⇓ st1, from !E_Seq (!E_Ass rfl) (!E_Ass rfl),
  assert H2: c2 / empty_state ⇓ st2, from !E_Seq (!E_Ass rfl) (!E_Ass rfl),

  have Hcontra: st1 = st2, by apply (!ceval_deterministic H1); rewrite -c12 at H2; apply H2,
  have neq: 1 = 2, from calc
    1 = st1 Y : rfl
    ... = st2 Y : congr_fun Hcontra Y
    ... = 2 : rfl,
  show false, from succ_ne_self (neq ⁻¹)
qed

-- Exercise: 4 stars, optional (better_subst_equiv)
inductive var_not_used_in_aexp (X : ident) : aexp → Prop :=
| VNUNum: ∀n, var_not_used_in_aexp X (ANum n)
| VNUId: ∀Y, X ≠ Y → var_not_used_in_aexp X (AId Y)
| VNUPlus: ∀a1 a2,
  var_not_used_in_aexp X a1 →
  var_not_used_in_aexp X a2 →
  var_not_used_in_aexp X (APlus a1 a2)
| VNUMinus: ∀a1 a2,
  var_not_used_in_aexp X a1 →
  var_not_used_in_aexp X a2 →
  var_not_used_in_aexp X (AMinus a1 a2)
| VNUMult: ∀a1 a2,
  var_not_used_in_aexp X a1 →
  var_not_used_in_aexp X a2 →
  var_not_used_in_aexp X (AMult a1 a2)

lemma aeval_weakening : ∀i st a ni,
  var_not_used_in_aexp i a →
  aeval (update st i ni) a = aeval st a :=
begin
  intros,
  induction a_1,
    unfold aeval,
    unfold aeval, unfold update, rewrite (if_neg a),
    unfold aeval, rewrite [v_0, v_1],
    unfold aeval, rewrite [v_0, v_1],
    unfold aeval, rewrite [v_0, v_1]    
end

-- Exercise: 3 stars, optional (inequiv_exercise)
theorem inequiv_exercise: 
  ¬ cequiv (WHILE BTrue DO SKIP END) SKIP :=
begin
  intro, unfold cequiv at a,
  apply (WHILE_true_nonterm BTrue SKIP empty_state empty_state),
    apply refl_bequiv,
    rewrite (a empty_state empty_state),
    exact !E_Skip
end

end Equiv

namespace Himp

open - [notation] Idn
open Idn.aexp Idn.bexp

inductive com : Type :=
| CSkip : com
| CAss : ident → aexp → com
| CSeq : com → com → com
| CIf : bexp → com → com → com
| CWhile : bexp → com → com
| CHavoc : ident → com
open com

notation `SKIP` := CSkip
infix `::=`:800 := CAss
infixr `;;`:500 := CSeq
notation `WHILE` b `DO` c `END` := CWhile b c
notation `IFB` c1 `THEN` c2 `ELSE` c3 `FI` := CIf c1 c2 c3
prefix `HAVOC`:900 := CHavoc

-- Exercise: 2 stars (himp_ceval)
inductive ceval : com → states → states → Prop :=
| E_Skip : ∀ st, ceval SKIP st st
| E_Ass : ∀ st a1 n x, aeval st a1 = n → ceval (x ::= a1) st (update st x n)
| E_Seq : ∀ c1 c2 st st' st'', ceval c1 st st' → ceval c2 st' st'' → ceval (c1 ;; c2) st st''
| E_IfTrue : ∀ st st' b c1 c2, beval st b = tt → ceval c1 st st' → ceval (IFB b THEN c1 ELSE c2 FI) st st'
| E_IfFalse : ∀ st st' b c1 c2, beval st b = ff → ceval c2 st st' → ceval (IFB b THEN c1 ELSE c2 FI) st st'
| E_WhileEnd : ∀ b st c, beval st b = ff → ceval (WHILE b DO c END) st st
| E_WhileLoop : ∀ st st' st'' b c, beval st b = tt → ceval c st st' → ceval (WHILE b DO c END) st' st'' → ceval (WHILE b DO c END) st st''
| E_Havoc : ∀ st i n, ceval (HAVOC i) st (update st i n)
open ceval

notation c1 `/` st `⇓` st' := ceval c1 st st'

example : (HAVOC X) / empty_state ⇓ update empty_state X 0 := !E_Havoc
example : (SKIP;; HAVOC Z) / empty_state ⇓ update empty_state Z 42 := !E_Seq !E_Skip !E_Havoc

definition cequiv (c1 c2 : com) := ∀st st' : states, (c1 / st ⇓ st') ↔ (c2 / st ⇓ st')

-- Exercise: 3 stars (havoc_swap)
definition pXY := HAVOC X ;; HAVOC Y
definition pYX := HAVOC Y ;; HAVOC X

theorem pXY_cequiv_pYX : cequiv pXY pYX :=
assert hyp1: ∀st n n_1, (λ y, ite (Y = y) n (ite (X = y) n_1 (st y))) = update (update st Y n) X n_1, begin
  intros, unfold update, apply funext, intro,
  cases decidable.em (Y = x),
    rewrite [a, if_pos rfl, if_pos rfl, -a],
    rewrite [if_neg a, if_neg a]
end,
assert hyp2: ∀st n n_1, (λ y, ite (X = y) n_1 (ite (Y = y) n (st y))) = update (update st X n_1) Y n, begin
  intros, unfold update, apply funext, intro,
  cases decidable.em (Y = x),
    rewrite [a, if_pos rfl, if_pos rfl, -a],
    rewrite [if_neg a, if_neg a]
end,
begin
  intros, split,
    intro,
      cases a,
        cases a_2, cases a_1, fold X, fold Y,
        apply !E_Seq (E_Havoc _ _ n),
        rewrite (hyp1 st n n_1), apply !E_Havoc,
    intro,
      cases a,
        cases a_1, cases a_2, fold X, fold Y,
        apply !E_Seq (E_Havoc _ _ n_1),
        rewrite (hyp2 st n n_1), apply !E_Havoc
end

-- Exercise: 4 stars, optional (havoc_copy)
definition ptwice := HAVOC X;; HAVOC Y.
definition pcopy := HAVOC X;; Y ::= AId X.

theorem ptwice_cequiv_pcopy : ¬cequiv ptwice pcopy :=
proof
  take ceq,
  assert lem1: ∀st st', (Y ::= AId X / st ⇓ st') → st' = update st Y (st X), begin
    intros, cases a, unfold update, apply funext,
    intro, unfold aeval at a_1, rewrite -a_1
  end,

  let st1 := update (update empty_state X 0) Y 1 in

  assert p: ptwice / empty_state ⇓ st1, from !E_Seq !E_Havoc !E_Havoc,
  assert q: pcopy / empty_state ⇓ st1, by rewrite ceq at p; assumption,
  assert r: ∃n, (update (update empty_state X 0) Y 1) = update (update empty_state X n) Y n, begin
    cases q, cases a, fold X at a_1, existsi n, apply (!lem1 a_1)
  end,
  show false, begin
    apply (exists.elim r), intros,
    cases decidable.em (a = 0),
      rewrite [a_2 at a_1], apply (@succ_ne_self 0 (congr_fun a_1 Y)),
      apply (a_2 (congr_fun a_1 X)⁻¹)
  end
qed

-- Exercise: 5 stars, advanced (p1_p2_equiv)
definition p1 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC Y;;
    X ::= APlus (AId X) (ANum 1)
  END

definition p2 : com :=
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    SKIP
  END

lemma p1_may_diverge : ∀st st', st X ≠ 0 →
  ¬ p1 / st ⇓ st' := sorry
-- X ≥ 1がループ不変条件であることを示す

lemma p2_may_diverge : ∀st st', st X ≠ 0 →
  ¬ p2 / st ⇓ st' := sorry
-- X ≠ 0がループ不変条件であることを示す

theorem p1_p2_equiv : cequiv p1 p2 := sorry

-- Exercise: 4 stars, advanced (p3_p4_inquiv)
definition p3 : com :=
  Z ::= ANum 1;;
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    HAVOC X;;
    HAVOC Z
  END

definition p4 : com :=
  X ::= (ANum 0);;
  Z ::= (ANum 1).

theorem p3_p4_inequiv : ¬ cequiv p3 p4 := sorry
-- p3 / {} ⇓ {X := 0, Z := 2} による

-- Exercise: 5 stars, advanced, optional (p5_p6_equiv)
definition p5 : com :=
  WHILE (BNot (BEq (AId X) (ANum 1))) DO
    HAVOC X
  END

definition p6 : com :=
  X ::= ANum 1.

theorem p5_p6_equiv : cequiv p5 p6 := sorry
-- p5 / st ⇓ st' ↔ st' X = 1

end Himp

namespace Equiv2
open Idn Idn.aexp Idn.bexp Idn.com Idn.ceval

definition stequiv (st1 st2 : states) := ∀(X : ident), st1 X = st2 X

-- Exercise: 1 star, optional (stequiv_refl)
lemma stequiv_refl : ∀(st : states), stequiv st st := λst X, rfl

-- Exercise: 1 star, optional (stequiv_sym)
lemma stequiv_sym : ∀(st1 st2 : states), stequiv st1 st2 → stequiv st2 st1
:= λst1 st2 se X, (se X) ⁻¹

-- Exercise: 1 star, optional (stequiv_trans)
lemma stequiv_trans : ∀(st1 st2 st3 : states), 
  stequiv st1 st2 → 
  stequiv st2 st3 → 
  stequiv st1 st3 := λst1 st2 st3 se1 se2 X, se1 X ⬝ se2 X

-- Exercise: 1 star, optional (stequiv_update)
lemma stequiv_update : ∀(st1 st2 : states),
  stequiv st1 st2 → 
  ∀(X:ident) (n:nat),
  stequiv (update st1 X n) (update st2 X n) := λst1 st2 se1 X n Y,
begin
  unfold update,
  cases decidable.em (X = Y),
    rewrite [a, if_pos rfl, if_pos rfl],
    rewrite [if_neg a, if_neg a], apply !se1
end

-- Exercise: 2 stars, optional (stequiv_aeval)
lemma stequiv_aeval : ∀(st1 st2 : states), 
  stequiv st1 st2 →
  ∀(a:aexp), aeval st1 a = aeval st2 a := λst1 st2 se1 a,
begin
  unfold stequiv at se1,
  induction a,
    esimp,
    unfold aeval, apply (se1 a),
    unfold aeval, rewrite [v_0, v_1],
    unfold aeval, rewrite [v_0, v_1],
    unfold aeval, rewrite [v_0, v_1]
end

-- Exercise: 2 stars, optional (stequiv_beval)
lemma stequiv_beval : ∀(st1 st2 : states), 
  stequiv st1 st2 →
  ∀(b:bexp), beval st1 b = beval st2 b := λst1 st2 se1 b,
begin
  unfold stequiv at se1,
  induction b,
    unfold beval, unfold beval,
    unfold beval, rewrite [!stequiv_aeval se1, !stequiv_aeval se1],
    unfold beval, rewrite [!stequiv_aeval se1, !stequiv_aeval se1],
    unfold beval, rewrite v_0,
    unfold beval, rewrite [v_0, v_1]
end

lemma stequiv_ceval_lemma : ∀c st1 st1',
  (c / st1 ⇓ st1') →
  ∀st2, stequiv st1 st2 → ∀st2', (c / st2 ⇓ st2') → stequiv st1' st2' :=
begin
  intros c st1 st1' ce,
  induction ce,
    intros, cases a_1, apply a,
    intros st2 a_1 st2' a_2 X1, cases a_2,
      have update st x n X1 = update st2 x n_1 X1,
      begin
        rewrite [!stequiv_aeval a_1 at a, a_3 at a, a],
        apply (!stequiv_update a_1)
      end,
      unfold update, unfold update at this, assumption,
    intros, revert X,
      cases a_3,
      assert se2: stequiv st' st'_1, apply (v_0 _ a_2 _ a_4),
      apply (v_1 _ se2 _ a_5),
    intros, revert X,
      cases a_3,
        apply (v_0 _ a_2 _ a_5),
        rewrite [!stequiv_beval a_2 at a, a at a_4], contradiction,
    intros, revert X,
      cases a_3,
        rewrite [!stequiv_beval a_2 at a, a at a_4], contradiction,
        apply (v_0 _ a_2 _ a_5),
    intros, revert X,
      cases a_2,
        apply a_1,
        rewrite [!stequiv_beval a_1 at a, a at a_3], contradiction,
    intros, revert X,
      assert a_4': WHILE b DO c END / st2 ⇓ st2', assumption,
      cases a_4',
        rewrite [!stequiv_beval a_3 at a, a at a_5], contradiction,
        apply (v_1 _ (v_0 _ a_3 _ a_6) _ a_7)
end

lemma stequiv_ceval: ∀(st1 st2 : states),
  stequiv st1 st2 →
  ∀(c: com) (st1': states),
    (c / st1 ⇓ st1') →
    ∃st2' : states,
    ((c / st2 ⇓ st2') ∧ stequiv st1' st2') := sorry
/-
begin
  intros, generalize a, generalize st2,
  induction a_1,
    intros, existsi st2_1, split,
      apply !E_Skip, assumption,
    intros, existsi (update st2_1 x n), split,
      rewrite -a, apply !E_Ass, rewrite [!stequiv_aeval a_1],
      rewrite [-(!stequiv_aeval a_1), -(!stequiv_aeval a_2)],
      apply (!stequiv_update a_2),
    intros,
      cases (v_0 a_2 _ a_3),
      cases (v_0 a_2 _ a_2),
        
end
-/

/-
inductive ceval' : com → states → states → Prop :=
| E_equiv : ∀c st st' st'', (ceval' c st st') → 
  stequiv st' st'' → (ceval' c st st'')

notation c1 `/` st `⇓'` st' := ceval' c1 st st'

definition cequiv' (c1 c2 : com) : Prop :=
  ∀(st st' : states),
    (c1 / st ⇓' st') ↔ (c2 / st ⇓' st').
-/

-- Exercise: 2 stars, optional (identity_assignment')
-- Exercise: 4 stars, optional (for_while_equiv)
-- Exercise: 3 stars, optional (swap_noninterfering_assignments)


end Equiv2

