import Imp
open eq.ops nat bool
open Idn Idn.ident Idn.aexp Idn.bexp Idn.com Idn.ceval

definition Assertion := states → Prop

-- Exercise: 1 star, optional (assertions)
definition as1 : Assertion := λst, st X = 3
definition as2 : Assertion := λst, st X ≤ st Y
definition as3 : Assertion := λst, st X = 3 ∨ st X ≤ st Y
definition as4 : Assertion := λst, st Z * st Z ≤ st X ∧
  ¬ ((succ (st (Id zero)) * succ (st (Id zero))) ≤ st X)
definition as5 : Assertion := λst, true
definition as6 : Assertion := λst, false

definition assert_implies (P Q : Assertion) : Prop :=
  ∀st, P st → Q st

infix `↣`:1200 := assert_implies
infix `↭`:1200 := (λP Q, P ↣ Q ∧ Q ↣ P)

definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  ∀st st', (c / st ⇓ st') → P st → Q st'

notation `{{` P `}}` c `{{` Q `}}` := hoare_triple P c Q

-- Exercise: 1 star, optional (triples)
-- Exercise: 1 star, optional (valid_triples)

theorem hoare_post_true : ∀(P Q : Assertion) c,
  (∀st, Q st) → {{P}} c {{Q}} := λP Q c Qst st st' ce Pst, Qst st'

theorem hoare_pre_false : ∀(P Q : Assertion) c,
  (∀st, ¬ (P st)) → {{P}} c {{Q}} := λP C c nPst st st' ce Pst, not.elim (nPst st) Pst

definition assn_sub X a (P : Assertion) := λst, P (update st X (aeval st a))

notation P `[` X `↦` a `]` := (assn_sub X a P)

theorem hoare_asgn : ∀Q X a,
  {{Q [X ↦ a]}} (X ::= a) {{Q}} :=
begin
  intros Q X' a st st' a_1 a_2,
  assert t: st' = update st X' (aeval st a),
    cases a_1, unfold update, rewrite a_3,
  rewrite t, apply !a_2
end

lemma hoare_asgn_imp : ∀ P Q X a,
  (∀st, P st → Q [X ↦ a] st) →
  {{P}} (X ::= a) {{Q}} :=
begin
  intros,
  apply hoare_asgn, assumption,
  apply !a_1, assumption
end

example :
  {{(λst, st X = 3) [X ↦ ANum 3]}}
  (X ::= (ANum 3))
  {{(λst, st X = 3)}} := by apply hoare_asgn

-- Exercise: 2 stars (hoare_asgn_examples)
-- Exercise: 2 stars (hoare_asgn_wrong)
-- Exercise: 3 stars, advanced (hoare_asgn_fwd)
theorem hoare_asgn_fwd : ∀m a P,
  {{(λst, P st ∧ st X = m)}}
    X ::= a
  {{(λst, P (update st X m) ∧ st X = aeval (update st X m) a)}} :=
begin
  intros,
  assert s: st' = update st X (aeval st a),
    cases a_1, fold X, rewrite a_3,
  assert h1: update (update st X (aeval st a)) X m = st,
    begin
      rewrite [-(and.right a_2)], apply funext, intro,
      unfold update, cases decidable.em (X = x),
        rewrite [a_3, if_pos rfl],
        rewrite [if_neg a_3, if_neg a_3]
    end,
  split,
    rewrite [s, h1], apply (and.left a_2),
    rewrite [s, h1]
end

-- Exercise: 2 stars, advanced (hoare_asgn_fwd_exists)
theorem hoare_asgn_fwd_exists : ∀a P,
  {{(λst, P st)}}
    X ::= a
  {{(λst, ∃m, P (update st X m) ∧
                st X = aeval (update st X m) a)}} :=
begin
  intros,
  existsi (st X), 
  apply (!hoare_asgn_fwd a_1 (and.intro a_2 rfl))
end

theorem hoare_consequence_pre : ∀(P P' Q : Assertion) c,
  {{P'}} c {{Q}} →
  P ↣ P' →
  {{P}} c {{Q}} :=
begin
  intros, apply (!a a_2 (!a_1 a_3))
end

theorem hoare_consequence_post : ∀(P Q Q' : Assertion) c,
  {{P}} c {{Q'}} →
  Q' ↣ Q →
  {{P}} c {{Q}} :=
begin
  intros, apply (!a_1 (!a a_2 a_3))
end

example :
  {{(λst, true)}} (X ::= (ANum 1)) {{(λst, st X = 1)}} :=
begin
  intros, cases a, fold X, rewrite [if_pos rfl, -a_2]
end

theorem hoare_consequence : ∀(P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} →
  P ↣ P' →
  Q' ↣ Q →
  {{P}} c {{Q}} :=
begin
  intros,
  apply (!a_2 (!a a_3 (!a_1 a_4)))
end

-- Exercise: 2 stars (hoare_asgn_examples_2)
theorem hoare_skip : ∀P, {{P}} SKIP {{P}} :=
begin
  intros, cases a, assumption
end

theorem hoare_seq : ∀P Q R c1 c2,
  {{Q}} c2 {{R}} →
  {{P}} c1 {{Q}} →
  {{P}} c1;;c2 {{R}} :=
begin
  intros, cases a_2,
  apply (!a a_5), apply (!a_1 a_4), assumption
end

example : ∀a n,
  {{(λst, aeval st a = n)}}
  (X ::= a;; SKIP) 
  {{(λst, st X = n)}} :=
begin
  intros, cases a_1,
  cases a_3, cases a_4,
  rewrite [-a_2, a_1]
end

-- Exercise: 2 stars (hoare_asgn_example4)
example :
  {{(λst, true)}} (X ::= (ANum 1);; Y ::= (ANum 2)) 
  {{(λst, st X = 1 ∧ st Y = 2)}} :=
begin
  apply hoare_seq,
    apply hoare_asgn,
    intros,
      unfold assn_sub, split,
        unfold aeval, cases a, unfold aeval at a_2,
          rewrite -a_2,
        unfold aeval
end

-- Exercise: 3 stars (swap_exercise)
definition swap_program : com :=
  Z ::= AId Y ;;
  Y ::= AId X ;;
  X ::= AId Z

theorem swap_exercise :
  {{(λst, st X ≤ st Y)}} 
  swap_program
  {{(λst, st Y ≤ st X)}} :=
begin
  apply hoare_seq, apply hoare_seq,
  apply hoare_asgn, apply hoare_asgn,
  intros,
    cases a,
    assert p1: (λst, st Y ≤ st X)[X ↦ AId Z] = (λst, st Y ≤ st Z),
      unfold assn_sub,
    assert p2: (λst, st Y ≤ st Z)[Y ↦ AId X] = (λst, st X ≤ st Z),
      unfold assn_sub,
    rewrite [p1, p2, ↓Z, if_pos rfl],
    assert ZX : Z ≠ X,
      unfold Z, unfold X, intro, 
      rewrite Id_iff at a, contradiction,
    rewrite [if_neg ZX, ↑aeval at a_2, -a_2], assumption
end

-- Exercise: 3 stars (hoarestate1)

definition bassn (b : bexp) : Assertion := λst, beval st b = tt

lemma bexp_eval_true : ∀b st,
  beval st b = tt → (bassn b) st :=
begin
  intros, unfold bassn, assumption
end

lemma bexp_eval_false : ∀b st,
  beval st b = ff → ¬ ((bassn b) st) :=
begin
  intros, unfold bassn at a_1,
  rewrite a at a_1, contradiction
end

theorem hoare_if : ∀P Q b c1 c2,
  {{(λst, P st ∧ bassn b st)}} c1 {{Q}} →
  {{(λst, P st ∧ ¬(bassn b st))}} c2 {{Q}} →
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}} :=
begin
  intros, cases a_2,
    apply a, apply a_5,
    split, assumption,
      unfold bassn, assumption,
    apply a_1, apply a_5,
    split, assumption,
      intro, unfold bassn at a_2, rewrite a_2 at a_4, contradiction
end

example : 
    {{(λst, true)}}
  IFB (BEq (AId X) (ANum 0)) 
    THEN (Y ::= (ANum 2)) 
    ELSE (Y ::= APlus (AId X) (ANum 1)) 
  FI
    {{(λst, st X ≤ st Y)}} :=
begin
  apply hoare_if,
    apply hoare_asgn_imp,
      intros,
      assert h: (λst, st X ≤ st Y)[Y ↦ ANum 2] st = (st X ≤ 2),
        unfold assn_sub,
      rewrite [h, ↑bassn at a, ↑beval at a, ↑aeval at a],
      assert stX: st X = 0,
        generalize (and.right a), induction (st X),
          intro, esimp,
          contradiction,
      assert k: (0 : nat) ≤ 2, simp,
      rewrite -stX at k, assumption,
    apply hoare_asgn_imp,
      intros,
      unfold bassn at a, unfold beval at a, unfold aeval at a,
      assert h: (λ (st : states), st X ≤ st Y)[Y↦APlus (AId X) (ANum 1)] = (λst, st X ≤ st X + 1),
        unfold assn_sub, rewrite h, apply le_add_right
end

-- Exercise: 2 stars (if_minus_plus)
theorem if_minus_plus :
  {{(λst, true)}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{(λst, st Y = st X + st Z)}} :=
begin
  apply hoare_if,
    apply hoare_asgn_imp,
      intros,
      assert YZ: Y ≠ Z, intro, rewrite [↑Y at a_1, ↑Z at a_1, Id_iff at a_1], apply (succ_ne_self (a_1⁻¹)),
      assert XZ: X ≠ Z, intro, rewrite [↑X at a_1, ↑Z at a_1, Id_iff at a_1], contradiction,
      assert h: (λst, st Y = st X + st Z)[Z↦AMinus (AId Y) (AId X)] st = (st Y = st X + (st Y - st X)),
        unfold assn_sub,
      rewrite [h, ↑bassn at a, ↑beval at a, ↑aeval at a],
      assert h2: st X ≤ st Y,
        apply ble_nat_le, apply (and.right a),
      apply ((add_sub_of_le h2)⁻¹),
    apply hoare_asgn_imp,
      intros,
      assert h: (λst, st Y = st X + st Z)[Y↦APlus (AId X) (AId Z)] st = (st X + st Z = st X + st Z),
        unfold assn_sub,
      rewrite h
end

-- Exercise: 4 stars (if1_hoare)
namespace If1
end If1

/-
-- use well-founded recursion

lemma hoare_while_lem : ∀P b c,
  {{(λst, P st ∧ bassn b st)}} c {{P}} →
  ∀ st st', (WHILE b DO c END / st ⇓ st') → P st → P st' ∧ ¬ (bassn b st')
| P b c hyp st st (E_WhileEnd b st c bev) := λPst, and.intro Pst (λbevt, by rewrite [↑bassn at bevt, bev at bevt]; contradiction)
| P b c hyp st st' (E_WhileLoop st st₁ st' b c bev cevc cevw) := λPst, hoare_while_lem _ _ _ hyp _ _ cevw (hyp _ _ cevc (and.intro Pst bev))
-/

lemma hoare_while : ∀P b c,
  {{(λst, P st ∧ bassn b st)}} c {{P}} →
  {{P}} WHILE b DO c END {{(λst, P st ∧ ¬ (bassn b st))}} := sorry

