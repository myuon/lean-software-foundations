import data

inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day
open day

definition next_weekday : day → day
| monday := tuesday
| tuesday := wednesday
| wednesday := thursday
| thursday := friday
| friday := monday
| saturday := monday
| sunday := monday

eval (next_weekday friday)
eval (next_weekday (next_weekday saturday))

example : ((next_weekday (next_weekday saturday)) = tuesday) := rfl

open bool

-- Exercise: 1 star (nandb)

definition nandb : bool → bool → bool
| tt tt := ff
| _ _ := tt

example : nandb tt ff = tt := rfl
example : nandb ff ff = tt := rfl
example : nandb ff tt = tt := rfl
example : nandb tt tt = ff := rfl

-- Exercise: 1 star (andb3)
definition andb3 : bool → bool → bool → bool
| a b c := a && b && c

check bnot

open nat

definition pred : nat → nat
| zero := zero
| (succ n) := n

definition minustwo : nat → nat
| zero := zero
| (succ zero) := zero
| (succ (succ n)) := n

eval minustwo 4

definition evenb : nat → bool
| zero := tt
| (succ zero) := ff
| (succ (succ n)) := evenb n

definition oddb n := bnot (evenb n)

example : oddb 1 = tt := rfl
example : oddb 4 = ff := rfl

-- Exercise: 1 star (factorial)
definition factorial : nat → nat
| 0 := 1
| (succ n) := (succ n) * factorial n

eval (0 : nat) + 1 + 1

definition beq_nat : nat → nat → bool
| 0 0 := tt
| 0 (succ m) := ff
| (succ n) 0 := ff
| (succ n) (succ m) := beq_nat n m

lemma beq_nat_eq : ∀ n m, beq_nat n m = tt → n = m
| 0 0 := λe, rfl
| 0 (succ m) := by intro; contradiction
| (succ n) 0 := by intro; contradiction
| (succ n) (succ m) := λe, congr_arg succ (beq_nat_eq n m e)

definition ble_nat : nat → nat → bool
| 0 _ := tt
| (succ n) 0 := ff
| (succ n) (succ m) := ble_nat n m

lemma ble_nat_le : ∀ n m, ble_nat n m = tt → n ≤ m
| 0 m := λe, !zero_le
| (succ n) 0 := by intro; contradiction
| (succ n) (succ m) := λe, succ_le_succ (ble_nat_le n m e)

-- Exercise: 2 stars (blt_nat)
definition blt_nat (n m : nat) : bool := ble_nat n m && (bnot (beq_nat n m))

example : blt_nat 2 2 = ff := rfl
example : blt_nat 2 4 = tt := rfl
example : blt_nat 4 2 = ff := rfl

theorem plus_0_r (n : nat) : n + 0 = n := rfl
theorem plus_1_r (n : nat) : n + 1 = succ n := rfl
theorem mult_0_r (n : nat) : n * 0 = 0 := rfl

-- Exercise: 1 star (plus_id_exercise)
theorem plus_id_exercise (n m o : nat) : n = m → m = o → n + m = m + o :=
begin
  intro p q,
  rewrite p,
  rewrite q
end

theorem mult_0_plus (n m : nat) : (n + 0) * m = n * m := rfl

-- Exercise: 2 stars (mult_S_1)
theorem mult_s_1 (n m : nat) : m = succ n → m * (n + 1) = m * m :=
begin
  intro p,
  rewrite plus_1_r,
  rewrite p
end

theorem plus_1_neq_0 (n : nat) : beq_nat (n + 1) 0 = ff := rfl
theorem bnot_involutive (b : bool) : bnot (bnot b) = b :=
begin
  cases b,
  apply rfl, apply rfl
end

-- Exercise: 1 star (zero_nbeq_plus_1)
theorem zeo_nbeq_plus_1 (n : nat) : beq_nat 0 (n + 1) = ff := rfl

-- Exercise: 2 stars (boolean_functions)
theorem identity_fn_applied_twice : ∀ (f : bool → bool), (∀x, f x = x) → ∀b, f (f b) = b :=
begin
  intros,
  rewrite a,
  rewrite a
end

-- Exercise: 2 stars (andb_eq_orb)
theorem andb_eq_orb : ∀ (b c : bool), (b && c = b || c) → b = c
| tt c p := calc
  tt = tt || c : tt_bor
  ... = tt && c : p
  ... = c : tt_band
| ff c p := calc
  ff = ff && c : ff_band
  ... = ff || c : p
  ... = c : ff_bor

-- Exercise: 3 stars (binary)
inductive bin :=
| zero : bin
| twice : bin → bin
| twice_one : bin → bin

definition incr : bin → bin
| bin.zero := bin.twice_one bin.zero
| (bin.twice b) := bin.twice_one b
| (bin.twice_one b) := bin.twice (incr b)

definition bin_nat : bin → nat
| bin.zero := zero
| (bin.twice b) := 2 * bin_nat b
| (bin.twice_one b) := 2 * bin_nat b + 1


