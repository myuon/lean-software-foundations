import Imp
open eq.ops bool AExp Idn
open Idn.aexp Idn.bexp Idn.com Idn.ceval

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
  cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END) := begin
  intros,
  
end

