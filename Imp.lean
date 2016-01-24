import Basics Induction
open nat bool eq.ops list

namespace AExp
inductive aexp : Type :=
| ANum : nat → aexp
| APlus : aexp → aexp → aexp
| AMinus : aexp → aexp → aexp
| AMult : aexp → aexp → aexp
open aexp

inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp → aexp → bexp
| BLe : aexp → aexp → bexp
| BNot : bexp → bexp
| BAnd : bexp → bexp → bexp
open bexp

definition aeval : aexp → nat
| (ANum n) := n
| (APlus a1 a2) := aeval a1 + aeval a2
| (AMinus a1 a2) := aeval a1 - aeval a2
| (AMult a1 a2) := aeval a1 * aeval a2

example : aeval (APlus (ANum 2) (ANum 2)) = 4 := rfl

definition beval : bexp → bool
| BTrue := tt
| BFalse := ff
| (BEq a1 a2) := beq_nat (aeval a1) (aeval a2)
| (BLe a1 a2) := ble_nat (aeval a1) (aeval a2)
| (BNot b1) := bnot (beval b1)
| (BAnd b1 b2) := band (beval b1) (beval b2)

definition optimize_0plus : aexp → aexp
| (ANum n) := ANum n
| (APlus (ANum 0) a2) := optimize_0plus a2
| (APlus a1 a2) := APlus (optimize_0plus a1) (optimize_0plus a2)
| (AMinus a1 a2) := AMinus (optimize_0plus a1) (optimize_0plus a2)
| (AMult a1 a2) := AMult (optimize_0plus a1) (optimize_0plus a2)

example :
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1) := rfl

theorem optimize_0plus_sound : ∀ a, aeval (optimize_0plus a) = aeval a
| (ANum n) := rfl
| (APlus (ANum 0) a2) := calc
  aeval (optimize_0plus (APlus (ANum 0) a2)) = aeval (optimize_0plus a2) : rfl
  ... = aeval a2 : optimize_0plus_sound
  ... = aeval (APlus (ANum 0) a2) : plus_0_l
| (APlus (ANum (succ n)) a2) := calc
  aeval (optimize_0plus (APlus (ANum (succ n)) a2)) = succ n + aeval (optimize_0plus a2) : rfl
  ... = (succ n) + aeval a2 : optimize_0plus_sound a2
| (APlus (APlus a11 a12) a2) := calc
  aeval (optimize_0plus (APlus (APlus a11 a12) a2)) = aeval (optimize_0plus (APlus a11 a12)) + aeval (optimize_0plus a2) : rfl
  ... = aeval (APlus a11 a12) + aeval (optimize_0plus a2) : optimize_0plus_sound (APlus a11 a12)
  ... = aeval (APlus a11 a12) + aeval a2 : optimize_0plus_sound a2
| (APlus (AMinus a11 a12) a2) := calc
  aeval (optimize_0plus (APlus (AMinus a11 a12) a2)) = aeval (optimize_0plus (AMinus a11 a12)) + aeval (optimize_0plus a2) : rfl
  ... = aeval (AMinus a11 a12) + aeval (optimize_0plus a2) : optimize_0plus_sound (AMinus a11 a12)
  ... = aeval (AMinus a11 a12) + aeval a2 : optimize_0plus_sound a2
| (APlus (AMult a11 a12) a2) := calc
  aeval (optimize_0plus (APlus (AMult a11 a12) a2)) = aeval (optimize_0plus (AMult a11 a12)) + aeval (optimize_0plus a2) : rfl
  ... = aeval (AMult a11 a12) + aeval (optimize_0plus a2) : optimize_0plus_sound (AMult a11 a12)
  ... = aeval (AMult a11 a12) + aeval a2 : optimize_0plus_sound a2
| (AMinus a1 a2) := calc
  aeval (optimize_0plus (AMinus a1 a2)) = aeval (optimize_0plus a1) - aeval (optimize_0plus a2) : rfl
  ... = aeval a1 - aeval (optimize_0plus a2) : optimize_0plus_sound a1
  ... = aeval a1 - aeval a2 : optimize_0plus_sound a2
| (AMult a1 a2) := calc
  aeval (optimize_0plus (AMult a1 a2)) = aeval (optimize_0plus a1) * aeval (optimize_0plus a2) : rfl
  ... = aeval a1 * aeval (optimize_0plus a2) : optimize_0plus_sound a1
  ... = aeval a1 * aeval a2 : optimize_0plus_sound a2

-- Exercise: 3 stars (optimize_0plus_b)
definition optimize_0plus_b : bexp → bexp
| (BEq a1 a2) := BEq (optimize_0plus a1) (optimize_0plus a2)
| (BLe a1 a2) := BLe (optimize_0plus a1) (optimize_0plus a2)
| (BNot b1) := BNot (optimize_0plus_b b1)
| (BAnd b1 b2) := BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
| b := b

theorem optimize_0plus_b_sound : ∀ b, beval (optimize_0plus_b b) = beval b
| BTrue := rfl
| BFalse := rfl
| (BEq a1 a2) := calc
  beval (optimize_0plus_b (BEq a1 a2)) = beq_nat (aeval (optimize_0plus a1)) (aeval (optimize_0plus a2)) : rfl
  ... = beq_nat (aeval a1) (aeval a2) : optimize_0plus_sound a2 ▸ rfl ⬝ optimize_0plus_sound a1 ▸ rfl
| (BLe a1 a2) := calc
  beval (optimize_0plus_b (BLe a1 a2)) = ble_nat (aeval (optimize_0plus a1)) (aeval (optimize_0plus a2)) : rfl
  ... = ble_nat (aeval a1) (aeval a2) : optimize_0plus_sound a2 ▸ rfl ⬝ optimize_0plus_sound a1 ▸ rfl
| (BNot b1) := calc
  beval (optimize_0plus_b (BNot b1)) = bnot (beval (optimize_0plus_b b1)) : rfl
  ... = bnot (beval b1) : optimize_0plus_b_sound b1
| (BAnd b1 b2) := calc
  beval (optimize_0plus_b (BAnd b1 b2)) = band (beval (optimize_0plus_b b1)) (beval (optimize_0plus_b b2)) : rfl
  ... = band (beval b1) (beval b2) : optimize_0plus_b_sound b2 ▸ rfl ⬝ optimize_0plus_b_sound b1 ▸ rfl

-- Exercise: 4 stars, optional (optimizer)
definition optimize_false_and : bexp → bexp
| BTrue := BTrue
| BFalse := BFalse
| (BEq a1 a2) := BEq a1 a2
| (BLe a1 a2) := BLe a1 a2
| (BNot b1) := BNot (optimize_false_and b1)
| (BAnd BTrue b2) := (optimize_false_and b2)
| (BAnd BFalse b2) := BFalse
| (BAnd b1 b2) := BAnd (optimize_false_and b1) (optimize_false_and b2)

theorem optimize_false_and_sound : ∀ b, beval (optimize_false_and b) = beval b
| BTrue := rfl
| BFalse := rfl
| (BEq a1 a2) := rfl
| (BLe a1 a2) := rfl
| (BNot b1) := calc
  beval (optimize_false_and (BNot b1)) = bnot (beval (optimize_false_and b1)) : rfl
  ... = bnot (beval b1) : optimize_false_and_sound b1
| (BAnd BTrue b2) := calc
  beval (optimize_false_and (BAnd BTrue b2)) = beval (optimize_false_and b2) : rfl
  ... = beval b2 : optimize_false_and_sound
  ... = beval (BAnd BTrue b2) : tt_band
| (BAnd BFalse b2) := calc
  beval (optimize_false_and (BAnd BFalse b2)) = ff : rfl
  ... = ff && beval b2 : ff_band
  ... = beval (BAnd BFalse b2) : rfl
| (BAnd (BEq b11 b12) b2) := calc
  beval (optimize_false_and (BAnd (BEq b11 b12) b2)) = beval (BAnd (optimize_false_and (BEq b11 b12)) (optimize_false_and b2)) : rfl
  ... = (beval (BEq b11 b12)) && (beval b2) : optimize_false_and_sound b2 ▸ rfl ⬝ optimize_false_and_sound (BEq b11 b12) ▸ rfl
| (BAnd (BLe b11 b12) b2) := calc
  beval (optimize_false_and (BAnd (BLe b11 b12) b2)) = beval (BAnd (optimize_false_and (BLe b11 b12)) (optimize_false_and b2)) : rfl
  ... = (beval (BLe b11 b12)) && (beval b2) : optimize_false_and_sound b2 ▸ rfl ⬝ optimize_false_and_sound (BLe b11 b12) ▸ rfl
| (BAnd (BNot b11) b2) := calc
  beval (optimize_false_and (BAnd (BNot b11) b2)) = beval (BAnd (optimize_false_and (BNot b11)) (optimize_false_and b2)) : rfl
  ... = (beval (BNot b11)) && (beval b2) : optimize_false_and_sound b2 ▸ rfl ⬝ optimize_false_and_sound (BNot b11) ▸ rfl
| (BAnd (BAnd b11 b12) b2) := calc
  beval (optimize_false_and (BAnd (BAnd b11 b12) b2)) = beval (BAnd (optimize_false_and (BAnd b11 b12)) (optimize_false_and b2)) : rfl
  ... = (beval (BAnd b11 b12)) && (beval b2) : optimize_false_and_sound b2 ▸ rfl ⬝ optimize_false_and_sound (BAnd b11 b12) ▸ rfl

inductive aevalR : aexp → nat → Prop :=
| E_ANum : ∀ (n : nat), aevalR (ANum n) n
| E_APlus : ∀ (e1 e2 : aexp) (n1 n2 : nat), aevalR e1 n1 → aevalR e2 n2 → aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus : ∀ (e1 e2 : aexp) (n1 n2 : nat), aevalR e1 n1 → aevalR e2 n2 → aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult : ∀ (e1 e2 : aexp) (n1 n2 : nat), aevalR e1 n1 → aevalR e2 n2 → aevalR (AMult e1 e2) (n1 * n2)
open aevalR

infix `⇓`:50 := aevalR

theorem aeval_iff_aevalR : ∀ a n, (a ⇓ n) ↔ aeval a = n :=
begin
  intros,
  split,
  intro,
  induction a_1,
    esimp,
    unfold aeval, rewrite [v_0, v_1],
    unfold aeval, rewrite [v_0, v_1],
    unfold aeval, rewrite [v_0, v_1],
  intro,
  cases a_1,
  induction a,
    apply E_ANum,
    apply E_APlus, apply v_0, apply v_1,
    apply E_AMinus, apply v_0, apply v_1,
    apply E_AMult, apply v_0, apply v_1
end

corollary aevalR_aeval : ∀ (a : aexp), aevalR a (aeval a) := λa, iff.elim_right !aeval_iff_aevalR rfl

inductive bevalR : bexp → bool → Prop :=
| E_BTrue : bevalR BTrue tt
| E_BFalse : bevalR BFalse ff
| E_BEq : ∀ (a1 a2 : aexp) (n1 n2 : nat), aevalR a1 n1 → aevalR a2 n2 → bevalR (BEq a1 a2) (beq_nat n1 n2)
| E_BLe : ∀ (a1 a2 : aexp) (n1 n2 : nat), aevalR a1 n1 → aevalR a2 n2 → bevalR (BLe a1 a2) (ble_nat n1 n2)
| E_BNot : ∀ b1 r1, bevalR b1 r1 → bevalR (BNot b1) (bnot r1)
| E_BAnd : ∀ b1 b2 r1 r2, bevalR b1 r1 → bevalR b2 r2 → bevalR (BAnd b1 b2) (r1 && r2)
open bevalR

theorem beval_iff_bevalR : ∀ b r, (bevalR b r) ↔ beval b = r :=
λb r, iff.intro
  (λbr, bevalR.rec_on br
    rfl rfl
    (λa1 a2 n1 n2 a1n1 a2n2, calc
      beval (BEq a1 a2) = beq_nat n1 (aeval a2) : iff.elim_left !aeval_iff_aevalR a1n1 ▸ rfl
      ... = beq_nat n1 n2 : iff.elim_left !aeval_iff_aevalR a2n2 ▸ rfl)
    (λa1 a2 n1 n2 a1n1 a2n2, calc
      beval (BLe a1 a2) = ble_nat n1 (aeval a2) : iff.elim_left !aeval_iff_aevalR a1n1 ▸ rfl
      ... = ble_nat n1 n2 : iff.elim_left !aeval_iff_aevalR a2n2 ▸ rfl)
    (λb1 r1 s b1r1, calc
      beval (BNot b1) = bnot r1 : b1r1 ▸ rfl)
    (λb1 b2 r1 r2 s1 s2 b1r1 b2r2, calc
      beval (BAnd b1 b2) = beval b1 && beval b2 : rfl
      ... = r1 && r2 : b1r1 ▸ b2r2 ▸ rfl))
  (proof
    suffices ∀ r, beval b = r → bevalR b r, by simp,
    (bexp.rec_on b
      (λr k, k ▸ E_BTrue)
      (λr k, k ▸ E_BFalse)
      (λr a1 a2 k, k ▸ !E_BEq !aevalR_aeval !aevalR_aeval)
      (λr a1 a2 k, k ▸ !E_BLe !aevalR_aeval !aevalR_aeval)
      (λa k1 r k2, !bnot_bnot ▸ E_BNot a (bnot r) (k1 (bnot r) (k2 ▸ !bnot_bnot ▸ rfl)))
      (λa1 a2 k1 k2 r s, s ▸ E_BAnd a1 a2 (beval a1) (beval a2) (k1 (beval a1) rfl) (k2 (beval a2) rfl)))
  qed)
end AExp

namespace aevalR_division
inductive aexp : Type :=
| ANum : nat → aexp
| APlus : aexp → aexp → aexp
| AMinus : aexp → aexp → aexp
| AMult : aexp → aexp → aexp
| ADiv : aexp → aexp → aexp
open aexp

inductive aevalR : aexp → nat → Prop :=
| E_ANum : ∀ (n : nat), aevalR (ANum n) n
| E_APlus : ∀ (e1 e2 : aexp) (n1 n2 : nat), aevalR e1 n1 → aevalR e2 n2 → aevalR (APlus e1 e2) (n1 + n2)
| E_AMinus : ∀ (e1 e2 : aexp) (n1 n2 : nat), aevalR e1 n1 → aevalR e2 n2 → aevalR (AMinus e1 e2) (n1 - n2)
| E_AMult : ∀ (e1 e2 : aexp) (n1 n2 : nat), aevalR e1 n1 → aevalR e2 n2 → aevalR (AMult e1 e2) (n1 * n2)
| E_ADiv : ∀ (a1 a2 : aexp) (n2 n3 : nat), aevalR a1 (n2 * n3) → aevalR a2 n2 → aevalR (ADiv a1 a2) n3
open aevalR

end aevalR_division

namespace Idn

inductive ident : Type :=
| Id : nat → ident
open ident

definition getId : ident → nat
| (Id n) := n

lemma getId_Id (a : nat) : getId (Id a) = a := begin
  induction a,
  esimp, esimp
end

lemma Id_iff (a b : nat) : Id a = Id b ↔ a = b :=
iff.intro
  (λk, congr_arg getId k ▸ (getId_Id a) ⁻¹ ▸ rfl)
  (λk, k ▸ rfl)

lemma getId_iff (a b : ident) : getId a = getId b ↔ a = b :=
iff.intro
  (ident.cases_on a (ident.cases_on b (λa1 a2, by rewrite getId_Id; rewrite getId_Id; simp)))
  (λk, k ▸ rfl)

theorem eq_id_dec [instance] : ∀ (id1 id2 : ident), decidable (id1 = id2) :=
λid1 id2, dite (getId id1 = getId id2)
  (λk, decidable.inl (iff.elim_left !getId_iff k))
  (λk, decidable.inr (implies.resolve (iff.elim_right !getId_iff) k))
reveal eq_id_dec

definition states := ident → nat
definition empty_state : states := λk, 0
definition update (st : states) (x : ident) (n : nat) : states :=
  λ (y : ident), if x = y then n else st y

-- Exercise: 1 star (update_eq)
theorem update_eq : ∀ n x st, (update st x n) x = n := λn x st, ident.cases_on x (λa, if_pos rfl)

-- Exercise: 1 star (update_neq)
theorem update_neq : ∀ x2 x1 n st, x2 ≠ x1 → (update st x2 n) x1 = st x1 :=
λx2 x1 n st neq, if_neg neq

-- Exercise: 1 star (update_example)
theorem update_example : ∀ (n : nat), update empty_state (Id 2) n (Id 3) = 0 := λn, if_neg (λk, succ_ne_self (iff.elim_left !Id_iff k ⁻¹))

-- Exercise: 1 star (update_shadow)
theorem update_shadow : ∀ n1 n2 x1 x2 st, update (update st x2 n1) x2 n2 x1 = (update st x2 n2) x1 := λn1 n2 x1 x2 st, calc
  update (update st x2 n1) x2 n2 x1 = if x2 = x1 then n2 else update st x2 n1 x1 : rfl
  ... = if x2 = x1 then n2 else st x1 : if_ctx_congr iff.rfl (λk, rfl) (λc, !update_neq c)
  ... = update st x2 n2 x1 : rfl

-- Exercise: 2 stars (update_same)
theorem update_same : ∀ n1 x1 x2 st, st x1 = n1 → update st x1 n1 x2 = st x2 := λn1 x1 x2 st k, dite (x1 = x2)
  (λeq, eq ▸ !update_eq ▸ k ▸ rfl)
  (λneq, !update_neq neq)

-- Exercise: 3 stars (update_permute)
theorem update_permute : ∀ n1 n2 x1 x2 x3 st, x2 ≠ x1 → update (update st x2 n1) x1 n2 x3 = update (update st x1 n2) x2 n1 x3 := λn1 n2 x1 x2 x3 st neq, begin
  unfold update,
  cases (decidable.em (x1 = x3)),
    rewrite a,
    rewrite (if_pos rfl),
    cases (decidable.em (x2 = x3)),
      exfalso, rewrite a at neq, apply (neq a_1),
      rewrite (if_neg a_1), rewrite (if_pos rfl),

    rewrite (if_neg a),
    cases (decidable.em (x2 = x3)),
      rewrite a_1, rewrite (if_pos rfl), rewrite (if_pos rfl),
      rewrite (if_neg a_1), rewrite (if_neg a_1), rewrite (if_neg a)
end

inductive aexp : Type :=
| ANum : nat → aexp
| AId : ident → aexp
| APlus : aexp → aexp → aexp
| AMinus : aexp → aexp → aexp
| AMult : aexp → aexp → aexp
open aexp

definition X : ident := Id 0
definition Y : ident := Id 1
definition Z : ident := Id 2

inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BEq : aexp → aexp → bexp
| BLe : aexp → aexp → bexp
| BNot : bexp → bexp
| BAnd : bexp → bexp → bexp
open bexp

definition aeval (st : states) : aexp → nat
| (ANum n) := n
| (AId x) := st x
| (APlus a1 a2) := aeval a1 + aeval a2
| (AMinus a1 a2) := aeval a1 - aeval a2
| (AMult a1 a2) := aeval a1 * aeval a2

definition beval (st : states) : bexp → bool
| BTrue := tt
| BFalse := ff
| (BEq a1 a2) := beq_nat (aeval st a1) (aeval st a2)
| (BLe a1 a2) := ble_nat (aeval st a1) (aeval st a2)
| (BNot b1) := bnot (beval b1)
| (BAnd b1 b2) := band (beval b1) (beval b2)

example :
  aeval (update empty_state X 5)
        (APlus (ANum 3) (AMult (AId X) (ANum 2)))
  = 13 := rfl

example :
  beval (update empty_state X 5)
        (BAnd BTrue (BNot (BLe (AId X) (ANum 4))))
  = tt := rfl

inductive com : Type :=
| CSkip : com
| CAss : ident → aexp → com
| CSeq : com → com → com
| CIf : bexp → com → com → com
| CWhile : bexp → com → com
open com

notation `SKIP` := CSkip
infix `::=`:800 := CAss
infixr `;;`:500 := CSeq
notation `WHILE` b `DO` c `END` := CWhile b c
notation `IFB` c1 `THEN` c2 `ELSE` c3 `FI` := CIf c1 c2 c3

definition fact_in_Lean : com :=
  Z ::= AId X;;
  Y ::= ANum 1;;
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    Y ::= AMult (AId Y) (AId Z);;
    Z ::= AMinus (AId Z) (ANum 1)
  END

definition plus2 : com :=
  X ::= (APlus (AId X) (ANum 2))

definition XtimesYinZ : com :=
  Z ::= (AMult (AId X) (AId Y))

definition subtract_slowly_body : com :=
  Z ::= AMinus (AId Z) (ANum 1) ;;
  X ::= AMinus (AId X) (ANum 1)

definition subtract_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    subtract_slowly_body
  END

definition subtract_3_from_5_slowly : com :=
  X ::= ANum 3 ;;
  Z ::= ANum 5 ;;
  subtract_slowly

definition loop : com :=
  WHILE BTrue DO
    SKIP
  END

definition ceval_fun_no_while : ∀ (st : states) (c : com), states
| st SKIP := st
| st (x ::= a1) := update st x (aeval st a1)
| st (c1 ;; c2) := ceval_fun_no_while (ceval_fun_no_while st c1) c2
| st (IFB b THEN c1 ELSE c2 FI) := if beval st b = tt then ceval_fun_no_while st c1 else ceval_fun_no_while st c2
| st (WHILE b DO c END) := st

inductive ceval : com → states → states → Prop :=
| E_Skip : ∀ st, ceval SKIP st st
| E_Ass : ∀ st a1 n x, aeval st a1 = n → ceval (x ::= a1) st (update st x n)
| E_Seq : ∀ c1 c2 st st' st'', ceval c1 st st' → ceval c2 st' st'' → ceval (c1 ;; c2) st st''
| E_IfTrue : ∀ st st' b c1 c2, beval st b = tt → ceval c1 st st' → ceval (IFB b THEN c1 ELSE c2 FI) st st'
| E_IfFalse : ∀ st st' b c1 c2, beval st b = ff → ceval c2 st st' → ceval (IFB b THEN c1 ELSE c2 FI) st st'
| E_WhileEnd : ∀ b st c, beval st b = ff → ceval (WHILE b DO c END) st st
| E_WhileLoop : ∀ st st' st'' b c, beval st b = tt → ceval c st st' → ceval (WHILE b DO c END) st' st'' → ceval (WHILE b DO c END) st st''
open ceval

notation c1 `/` st `⇓` st' := ceval c1 st st'

example :
    (X ::= ANum 2;;
     IFB BLe (AId X) (ANum 1)
       THEN Y ::= ANum 3
       ELSE Z ::= ANum 4
     FI)
   / empty_state
   ⇓ (update (update empty_state X 2) Z 4)
   := !E_Seq (!E_Ass rfl) (!E_IfFalse rfl (!E_Ass rfl))

-- Exercise: 2 stars (ceval_example2)
example :
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state ⇓
    (update (update (update empty_state X 0) Y 1) Z 2)
    := !E_Seq (!E_Ass rfl) (!E_Seq (!E_Ass rfl) (!E_Ass rfl))

-- Exercise: 3 stars, advanced (pup_to_n)
definition pup_to_n :=
  Y ::= ANum 0;;
  WHILE BLe (ANum 1) (AId X) DO
    Y ::= APlus (AId Y) (AId X);;
    X ::= AMinus (AId X) (ANum 1)
  END

theorem pup_to_2_ceval :
  pup_to_n / (update empty_state X 2) ⇓
    update (update (update (update (update (update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0 := begin
  unfold pup_to_n,
  apply E_Seq, apply (!E_Ass rfl),
  apply E_WhileLoop,
    apply rfl,
    apply E_Seq, apply (!E_Ass rfl), apply (!E_Ass rfl),
  apply E_WhileLoop,
    apply rfl,
    apply E_Seq, apply (!E_Ass rfl), apply (!E_Ass rfl),
  apply E_WhileEnd,
    apply rfl
end

lemma ceval_deterministic_lemma : ∀ c st st', (c / st ⇓ st') → ∀ u, (c / st ⇓ u) → st' = u :=
begin
  intro c st st' exp,
  induction exp,
    intros,
      cases a, esimp,
    intros,
      cases a_1, unfold update, apply funext, intro, 
      cases (decidable.em (x = x_1)),
        rewrite a_1,
          rewrite (if_pos rfl), rewrite (if_pos rfl),
          rewrite (a⁻¹), rewrite a_2,
        rewrite (if_neg a_1), rewrite (if_neg a_1),
    intros,
      cases a_2,
        rewrite ((!v_0 a_3)⁻¹) at a_4,
        rewrite (!v_1 a_4),
    intros,
      cases a_2,
        exact (!v_0 a_4),
        rewrite a at a_3, contradiction,
    intros,
      cases a_2,
        rewrite a at a_3, contradiction,
        exact (!v_0 a_4),
    intros,
      cases a_1,
        esimp,
        rewrite a at a_2, contradiction,
    intros,
      cases a_3,
        rewrite a at a_4, contradiction,
        rewrite ((!v_0 a_5)⁻¹) at a_6,
          exact (!v_1 a_6)
end

theorem ceval_deterministic : ∀ c st st1 st2, (c / st ⇓ st1) → (c / st ⇓ st2) → st1 = st2 := λc st st1 st2 e1 e2, !ceval_deterministic_lemma e1 _ e2

lemma n_neq_n_plus_2 : ∀ (n : nat), n ≠ n + 2 := proof
  take n,
  have Hp1: 0 ≠ 1, from (λk, !succ_ne_self (k⁻¹)),
  have Hp2: 0 ≠ 2, from
  proof
    take k,
    suffices 0 = 1, by exfalso; apply (Hp1 this),
    calc
      0 = pred 0 : rfl
      ... = pred 2 : k ▸ rfl
      ... = 1 : rfl
  qed,
  show n ≠ n + 2, from (λk, Hp2 (!nat.add_left_cancel k))
qed

theorem plus2_spec : ∀st n st',
  st X = n → (plus2 / st ⇓ st') → st' X = n + 2
:= begin
  intros,
  cases a_1,
    cases decidable.em (Id 0 = X),
      rewrite a_1,
        rewrite (if_pos rfl),
        rewrite (a_2 ⁻¹),
        rewrite (a ⁻¹),
      unfold X at a_1,
        exfalso,
        apply a_1,
        reflexivity
end

-- Exercise: 3 stars (XtimesYinZ_spec)
theorem XtimesYinZ_spec : ∀ st st',
  (XtimesYinZ / st ⇓ st') → st' Z = st X * st Y
:= begin
  intros,
  cases a,
    rewrite [↑Z, if_pos rfl, a_1⁻¹]
end

-- Exercise: 3 stars (loop_never_stops)
theorem ceval_induction_on_with : ∀ c st1 st2 (P : com → states → states → Prop),
  (c / st1 ⇓ st2) →
  (∀ st, P SKIP st st) →
  (∀ st a1 n x, aeval st a1 = n → P (x ::= a1) st (update st x n)) →
  (∀ c1 st st' c2 st'', (c1 / st ⇓ st') → P c1 st st' → (c2 / st' ⇓ st'') → P c2 st' st'' → P (c1 ;; c2) st st'') →
  (∀ st b c1 st' c2, beval st b = tt → (c1 / st ⇓ st') → P c1 st st' → P (IFB b THEN c1 ELSE c2 FI) st st') →
  (∀ st b c2 st' c1, beval st b = ff → (c2 / st ⇓ st') → P c2 st st' → P (IFB b THEN c1 ELSE c2 FI) st st') →
  (∀ st b c, beval st b = ff → P (WHILE b DO c END) st st) →
  (∀ st b c st' st'', beval st b = tt → (c / st ⇓ st') → P c st st' → (WHILE b DO c END / st' ⇓ st'') → P (WHILE b DO c END) st' st'' → P (WHILE b DO c END) st st'') →
  P c st1 st2
:= begin
  intros,
  induction a,
    apply a_1,
    apply a_2, apply a,
    apply a_3, apply a, apply v_0, apply a_8, apply v_1,
    apply a_4, apply a, apply a_8, apply v_0,
    apply a_5, apply a, apply a_8,
    cases decidable.em (beval st b = tt),
      repeat assumption,
      apply a_6, repeat assumption,
      apply a_7, repeat assumption
end

theorem while_induction : ∀ b c st st' (P : states → states → Prop),
  (WHILE b DO c END / st ⇓ st') →
  (∀ t, beval t b = ff → P t t) →
  (∀ t t' t'', beval t b = tt → (c / t ⇓ t') → (WHILE b DO c END / t' ⇓ t'') → P t' t'' → P t t'') →
  P st st'
:= λb c st st' P red base step,
  ceval_induction_on_with
    (WHILE b DO c END) st st'
    (λc0 t t', WHILE b DO c END = c0 → P t t') red
    (by contradiction) (by contradiction) (by contradiction)
    (by contradiction) (by contradiction)
    (by intros; apply base; cases a_1; exact a) (begin
      intros,
        apply step,
        cases a_5, exact a,
        cases a_5, exact a_1,
        cases a_5, cases a_5, exact a_3,
        apply a_4, exact a_5
    end) rfl

theorem loop_never_stops : ∀ st st', ¬ (loop / st ⇓ st') := proof
  take st st' r,
  show false,
  from while_induction BTrue SKIP st st' (λx y, false) r (by contradiction) (by simp)
qed

-- Exercise: 3 stars (no_whilesR)
definition no_whiles : com → bool
| SKIP := tt
| (_ ::= _) := tt
| (c1 ;; c2) := no_whiles c1 && no_whiles c2
| (IFB _ THEN ct ELSE cf FI) := no_whiles ct && no_whiles cf
| (WHILE _ DO _ END) := ff

inductive no_whilesR : com → Prop :=
| E_Skip : no_whilesR SKIP
| E_Ass : ∀ x a, no_whilesR (x ::= a)
| E_Seq : ∀ c1 c2, no_whilesR c1 → no_whilesR c2 → no_whilesR (c1 ;; c2)
| E_ITE : ∀ b c1 c2, no_whilesR c1 → no_whilesR c2 → no_whilesR (IFB b THEN c1 ELSE c2 FI)

theorem no_whiles_eqv : ∀ c, no_whiles c = tt ↔ no_whilesR c := begin
  intros,
  split,
    intro,
    induction c,
      exact no_whilesR.E_Skip,
      exact !no_whilesR.E_Ass,
      apply !no_whilesR.E_Seq,
        apply v_0,
        unfold no_whiles at a_2,
        exact (!band_elim_left a_2),
        unfold no_whiles at a_2,
        apply v_1,
        exact (!band_elim_right a_2),
      apply !no_whilesR.E_ITE,
        unfold no_whiles at a_3,
        apply v_0,
        exact (!band_elim_left a_3),
        apply v_1,
        exact (!band_elim_right a_3),
      unfold no_whiles at a_2,
        contradiction,
    intro,
    induction c,
      esimp, esimp, 
      unfold no_whiles,
        apply band_intro,
          apply v_0, cases a_2, exact a_3,
          apply v_1, cases a_2, exact a_4,
      unfold no_whiles,
        apply band_intro,
          apply v_0, cases a_3, exact a_4,
          apply v_1, cases a_3, exact a_5,
      cases a_2
end

-- Exercise: 4 stars (no_whiles_terminating)
theorem no_whiles_terminating : ∀ st com, no_whilesR com → ∃ st', com / st ⇓ st'
| st SKIP no_whilesR.E_Skip := exists.intro _ !E_Skip
| st (x ::= a) !no_whilesR.E_Ass := exists.intro _ (!E_Ass rfl)
| st (c1 ;; c2) (!no_whilesR.E_Seq e1 e2) :=
  obtain st1 (Hst1 : c1 / st ⇓ st1), from no_whiles_terminating st c1 e1,
  obtain st2 (Hst2 : c2 / st1 ⇓ st2), from no_whiles_terminating st1 c2 e2,
  exists.intro _ (!E_Seq Hst1 Hst2)
| st (IFB b THEN c1 ELSE c2 FI) (!no_whilesR.E_ITE e1 e2) :=
  obtain st1 (Hst1 : c1 / st ⇓ st1), from no_whiles_terminating st c1 e1,
  obtain st2 (Hst2 : c2 / st ⇓ st2), from no_whiles_terminating st c2 e2,
  @bool.cases_on
    (λx, beval st b = x → ∃st', (IFB b THEN c1 ELSE c2 FI / st⇓st')) _
    (λbe, exists.intro _ (!E_IfFalse be Hst2))
    (λbe, exists.intro _ (!E_IfTrue be Hst1)) rfl

-- Exercise: 3 stars (stack_compiler)
inductive sinstr :=
| SPush : nat → sinstr
| SLoad : ident → sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr
open sinstr

definition s_execute : states → list sinstr → list nat → list nat
| st [] l := l
| st (SPush n :: xs) l := s_execute st xs (n :: l)
| st (SLoad x :: xs) l := s_execute st xs (st x :: l)
| st (SPlus :: xs) [] := s_execute st xs []
| st (SPlus :: xs) [y] := s_execute st xs [y]
| st (SPlus :: xs) (y1 :: y2 :: ys) := s_execute st xs ((y2 + y1) :: ys)
| st (SMinus :: xs) [] := s_execute st xs []
| st (SMinus :: xs) [y] := s_execute st xs [y]
| st (SMinus :: xs) (y1 :: y2 :: ys) := s_execute st xs ((y2 - y1) :: ys)
| st (SMult :: xs) [] := s_execute st xs []
| st (SMult :: xs) [y] := s_execute st xs [y]
| st (SMult :: xs) (y1 :: y2 :: ys) := s_execute st xs ((y2 * y1) :: ys)

example :
  s_execute empty_state [SPush 5, SPush 3, SPush 1, SMinus] [] = [2, 5] := rfl

example :
  s_execute (update empty_state X 3) [SPush 4, SLoad X, SMult, SPlus] [3,4] = [15, 4] := rfl

definition s_compile : aexp → list sinstr
| (ANum n) := [SPush n]
| (AId x) := [SLoad x]
| (APlus y1 y2) := s_compile y1 ++ s_compile y2 ++ [SPlus]
| (AMinus y1 y2) := s_compile y1 ++ s_compile y2 ++ [SMinus]
| (AMult y1 y2) := s_compile y1 ++ s_compile y2 ++ [SMult]

lemma s_compile1 :
  s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y))) = [SLoad X, SPush 2, SLoad Y, SMult, SMinus] := rfl

-- Exercise: 3 stars, advanced (stack_compiler_correct)
theorem s_execute_app : ∀ (st : states) (l : list nat) (e1 e2 : list sinstr), s_execute st (e1 ++ e2) l = s_execute st e2 (s_execute st e1 l)
| st l [] e2 := rfl
| st l (SPush n :: xs) e2 := s_execute_app _ _ xs e2
| st l (SLoad n :: xs) e2 := s_execute_app _ _ xs e2
| st [] (SPlus :: xs) e2 := s_execute_app _ _ xs e2
| st [y] (SPlus :: xs) e2 := s_execute_app _ _ xs e2
| st (y1 :: y2 :: ys) (SPlus :: xs) e2 := s_execute_app _ _ xs e2
| st [] (SMinus :: xs) e2 := s_execute_app _ _ xs e2
| st [y] (SMinus :: xs) e2 := s_execute_app _ _ xs e2
| st (y1 :: y2 :: ys) (SMinus :: xs) e2 := s_execute_app _ _ xs e2
| st [] (SMult :: xs) e2 := s_execute_app _ _ xs e2
| st [y] (SMult :: xs) e2 := s_execute_app _ _ xs e2
| st (y1 :: y2 :: ys) (SMult :: xs) e2 := s_execute_app _ _ xs e2

theorem s_compile_correct_stack : ∀ (st : states) (e : aexp) (l : list nat),
  s_execute st (s_compile e) l = [aeval st e] ++ l
| st (ANum n) l := rfl
| st (AId x) l := rfl
| st (APlus a1 a2) l := calc
  s_execute st (s_compile (APlus a1 a2)) l = s_execute st (s_compile a1 ++ s_compile a2 ++ [SPlus]) l : rfl
  ... = s_execute st [SPlus] (s_execute st (s_compile a2) (s_execute st (s_compile a1) l)) : !s_execute_app ▸ !s_execute_app ▸ rfl
  ... = s_execute st [SPlus] ([aeval st a2] ++ ([aeval st a1] ++ l)) : !s_compile_correct_stack ▸ !s_compile_correct_stack ▸ rfl
  ... = s_execute st (SPlus :: []) (aeval st a2 :: aeval st a1 :: l) : rfl
  ... = s_execute st [] ((aeval st a1 + aeval st a2) :: l) : rfl
  ... = [aeval st (APlus a1 a2)] ++ l : rfl
| st (AMinus a1 a2) l := calc
  s_execute st (s_compile (AMinus a1 a2)) l = s_execute st (s_compile a1 ++ s_compile a2 ++ [SMinus]) l : rfl
  ... = s_execute st [SMinus] (s_execute st (s_compile a2) (s_execute st (s_compile a1) l)) : !s_execute_app ▸ !s_execute_app ▸ rfl
  ... = s_execute st [SMinus] ([aeval st a2] ++ ([aeval st a1] ++ l)) : !s_compile_correct_stack ▸ !s_compile_correct_stack ▸ rfl
  ... = s_execute st (SMinus :: []) (aeval st a2 :: aeval st a1 :: l) : rfl
  ... = s_execute st [] ((aeval st a1 - aeval st a2) :: l) : rfl
  ... = [aeval st (AMinus a1 a2)] ++ l : rfl
| st (AMult a1 a2) l := calc
  s_execute st (s_compile (AMult a1 a2)) l = s_execute st (s_compile a1 ++ s_compile a2 ++ [SMult]) l : rfl
  ... = s_execute st [SMult] (s_execute st (s_compile a2) (s_execute st (s_compile a1) l)) : !s_execute_app ▸ !s_execute_app ▸ rfl
  ... = s_execute st [SMult] ([aeval st a2] ++ ([aeval st a1] ++ l)) : !s_compile_correct_stack ▸ !s_compile_correct_stack ▸ rfl
  ... = s_execute st (SMult :: []) (aeval st a2 :: aeval st a1 :: l) : rfl
  ... = s_execute st [] ((aeval st a1 * aeval st a2) :: l) : rfl
  ... = [aeval st (AMult a1 a2)] ++ l : rfl

theorem s_compile_correct : ∀ (st : states) (e : aexp),
  s_execute st (s_compile e) [] = [aeval st e] := λst e, !s_compile_correct_stack

end Idn

-- Exercise: 5 stars, advanced (break_imp)
namespace BreakImp

open Idn (ident aexp bexp states aeval update beval empty_state)

inductive com : Type :=
| CSkip : com
| CBreak : com
| CAss : ident → aexp → com
| CSeq : com → com → com
| CIf : bexp → com → com → com
| CWhile : bexp → com → com
open com

notation `SKIP` := CSkip
notation `BREAK` := CBreak
infix `::=`:800 := CAss
infixr `;;`:500 := CSeq
notation `WHILE` b `DO` c `END` := CWhile b c
notation `IFB` c1 `THEN` c2 `ELSE` c3 `FI` := CIf c1 c2 c3

inductive status : Type :=
| SContinue : status
| SBreak : status
open status

inductive ceval : com → states → status → states → Prop :=
| E_Skip : ∀ st, ceval SKIP st SContinue st
| E_Break : ∀ st, ceval BREAK st SBreak st
| E_Ass : ∀ st a1 n x, aeval st a1 = n → ceval (x ::= a1) st SContinue (update st x n)
| E_Seq_Break : ∀ c1 c2 st st', ceval c1 st SBreak st' → ceval (c1 ;; c2) st SBreak st'
| E_Seq_Continue : ∀ c1 c2 st st' st'' s, ceval c1 st SContinue st' → ceval c2 st' s st'' → ceval (c1 ;; c2) st s st''
| E_IfTrue : ∀ st st' b c1 c2 s, beval st b = tt → ceval c1 st s st' → ceval (IFB b THEN c1 ELSE c2 FI) st s st'
| E_IfFalse : ∀ st st' b c1 c2 s, beval st b = ff → ceval c2 st s st' → ceval (IFB b THEN c1 ELSE c2 FI) st s st'
| E_WhileEnd : ∀ b st c, beval st b = ff → ceval (WHILE b DO c END) st SContinue st
| E_WhileLoop_Break : ∀ st st' b c, beval st b = tt → ceval c st SBreak st' → ceval (WHILE b DO c END) st SContinue st'
| E_WhileLoop_Continue : ∀ st st' st'' b c, beval st b = tt → ceval c st SContinue st' → ceval (WHILE b DO c END) st' SContinue st'' → ceval (WHILE b DO c END) st SContinue st''
open ceval

notation c1 `//` st `⇓` s `//` st' := ceval c1 st s st'

theorem break_ignore : ∀ c st st' s,
  ((BREAK ;; c) // st ⇓ s // st') → st = st' := λc st st' s r,
begin
  cases r,
    cases a, esimp, 
    cases a
end

theorem while_continue : ∀ b c st st' s,
  (WHILE b DO c END // st ⇓ s // st') →
  s = SContinue := λb c st st' s r,
begin
  cases r,
    esimp, esimp, esimp
end

theorem while_stops_on_break : ∀ b c st st',
  beval st b = tt →
  (c // st ⇓ SBreak // st') →
  (WHILE b DO c END // st ⇓ SContinue // st') := λb c st st' e1 e2,
begin
  apply E_WhileLoop_Break,
  exact e1,
  exact e2
end

-- Exercise: 3 stars, advanced, optional (while_break_true)
theorem while_break_true : ∀b c st st',
  (WHILE b DO c END // st ⇓ SContinue // st') →
  beval st' b = tt →
  ∃st'', c // st'' ⇓ SBreak // st'
:= sorry

-- Exercise: 4 stars, advanced, optional (ceval_deterministic)
lemma ceval_deterministic_lemma : ∀ c st s st', (c // st ⇓ s // st') → ∀ u s', (c // st ⇓ s' // u) → st' = u ∧ s = s' :=
proof
  take c st s st' r,

  assert lem1: ∀c1 st st', (∀ u s', (c1//st⇓s'//u) → st' = u ∧ SBreak = s') → (∃st'_1, c1//st⇓SContinue//st'_1) → false, proof
    take c1 st st' hyp ec,
    assert SBreak = SContinue, from exists.elim ec (λa h, and.elim_right (hyp _ _ h)),
    show false, by contradiction
  qed,

  assert lem2: ∀c1 st st', (∀ u s', (c1//st⇓s'//u) → st' = u ∧ SContinue = s') → (∃st'_1, c1//st⇓SBreak//st'_1) → false, proof
    take c1 st st' hyp ec,
    assert SContinue = SBreak, from exists.elim ec (λa h, and.elim_right (hyp _ _ h)),
    show false, by contradiction
  qed,

  show ∀ u s', (c // st ⇓ s' // u) → st' = u ∧ s = s', from
    ceval.induction_on r
      (λst s s' re, by cases re; simp)
      (λst u s' re, by cases re; simp)
      (λst u s' re, begin
        cases re, intros, split,
          cases a_2, unfold update, rewrite (a_1 ⁻¹), rewrite (a_3 ⁻¹),
          cases a_2, simp
      end)
      (λc1 c2 st1 st1' re hyp u s', status.cases_on s'
        (by intro; cases a; apply (false.elim (lem1 c1 st1 st1' hyp (by existsi st'_1; assumption))))
        (begin
          intro, cases a,
            apply (hyp _ _ a_1),
            apply (false.elim (lem1 c1 st1 st1' hyp (by existsi st'_1; assumption)))
        end))
      (begin
        intros,
        cases a_2,
          apply (false.elim (lem2 c1 st_1 st'_1 v_0 (by existsi u; assumption))),
          apply v_1,
            rewrite (and.elim_left (v_0 _ _ a_3)),
            exact a_4
      end)
      (begin
        intros,
        cases a_2,
          apply v_0, exact a_4,
          rewrite a at a_3, contradiction
      end)
      (begin
        intros,
        cases a_2,
          rewrite a at a_3, contradiction,
          apply v_0, exact a_4
      end) (begin
        intros,
        cases a_1,
          simp,
          rewrite a at a_2, contradiction,
          rewrite a at a_2, contradiction
      end) (begin
        intros,
        cases a_2,
          simp,
          split,
            apply (and.elim_left (v_0 _ _ a_4)), simp,
            apply (false.elim (lem1 c_1 st_1 st'_1 v_0 (by existsi st'_2; assumption)))
      end) (begin
        intros,
        cases a_3,
          rewrite a at a_4, contradiction,
          apply (false.elim (lem2 c_1 st_1 st'_1 v_0 (by existsi u; assumption))),
          rewrite ((and.elim_left (v_0 _ _ a_5))⁻¹) at a_6,
            apply v_1, exact a_6
      end)
qed

theorem ceval_deterministic : ∀c st st1 st2 s1 s2,
  (c // st ⇓ s1 // st1) → (c // st ⇓ s2 // st2) → st1 = st2 ∧ s1 = s2
:= λc st st1 st2 s1 s2 e1 e2, !ceval_deterministic_lemma e1 _ _ e2

-- Exercise: 3 stars, optional (short_circuit)
-- Exercise: 4 stars, optional (add_for_loop)

end BreakImp
