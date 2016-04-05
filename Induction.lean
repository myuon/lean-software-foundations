import Basics
open bool nat

-- Exercise: 2 stars (andb_true_elim2)
theorem andb_true_elim2 : ∀ (b c : bool), b && c = tt → c = tt
| tt c := λp, by rewrite tt_band at p; apply p
| ff c := λp, by contradiction

theorem plus_0_l : ∀ (n : nat), 0 + n = n
| zero := rfl
| (succ n) := calc
  0 + succ n = succ (0 + n) : rfl
  ... = succ n : plus_0_l

theorem minus_diag : ∀ (n : nat), n - n = 0
| zero := rfl
| (succ n) := calc
  succ n - succ n = n - n : succ_sub_succ
  ... = 0 : minus_diag

-- Exercise: 2 stars (basic_induction)
theorem mult_0_l : ∀ (n : nat), 0 * n = 0
| zero := rfl
| (succ n) := calc
  0 * succ n = 0 * n + 0 : rfl
  ... = 0 * n : rfl
  ... = 0 : mult_0_l

theorem plus_1_l : ∀ (n : nat), 1 + n = succ n
| zero := rfl
| (succ n) := calc
  1 + succ n = succ (1 + n) : rfl
  ... = succ (succ n) : plus_1_l

theorem plus_n_Sm : ∀ (n m : nat), succ (n + m) = n + succ m :=
take n m, rfl

theorem plus_Sn_m : ∀ (n m : nat), succ (n + m) = succ n + m :=
take n m, by rewrite succ_add

print plus_0_r

theorem plus_comm : ∀ (n m : nat), n + m = m + n
| n zero := calc
  n + 0 = n : plus_0_r n
  ... = 0 + n : plus_0_l n
| n (succ m) := calc
  n + succ m = succ (n + m) : plus_n_Sm
  ... = succ (m + n) : plus_comm
  ... = succ m + n : plus_Sn_m

theorem plus_assoc : ∀ (n m p : nat), n + (m + p) = (n + m) + p := by rec_simp

-- Exercise: 2 stars (double_plus)
definition double : nat → nat
| zero := zero
| (succ n) := succ (succ (double n))

lemma double_plus : ∀ (n : nat), double n = n + n
| zero := rfl
| (succ n) := calc
  double (succ n) = succ (succ (double n)) : rfl
  ... = succ (succ (n + n)) : double_plus
  ... = succ (succ n + n) : plus_Sn_m
  ... = succ n + succ n : rfl

-- Exercise: 1 star (destruct_induction)

-- Exercise: 4 stars (mult_comm)
theorem plus_swap : ∀ (n m p : nat), n + (m + p) = m + (n + p) := by simp

-- Exercise: 2 stars, optional (evenb_n__oddb_Sn)
lemma evenb_SS (n : nat) : evenb (succ (succ n)) = evenb n := rfl

theorem evenb_n_oddb_Sn : ∀ (n : nat), evenb n = bnot (evenb (succ n))
| zero := rfl
| (succ zero) := rfl
| (succ (succ n)) := calc
  evenb (succ (succ n)) = evenb n : evenb_SS
  ... = bnot (evenb (succ n)) : evenb_n_oddb_Sn
  ... = bnot (evenb (succ (succ (succ n)))) : evenb_SS

-- Exercise: 3 stars, optional (more_exercises)
-- Exercise: 2 stars, optional (beq_nat_refl)
-- Exercise: 2 stars, optional (plus_swap')

-- Exercise: 3 stars (binary_commute)
theorem bin_to_nat_pres_incr : ∀ (b : bin), bin_nat (incr b) = succ (bin_nat b)
| bin.zero := rfl
| (bin.twice b) := rfl
| (bin.twice_one b) := calc
  bin_nat (incr (bin.twice_one b)) = bin_nat (bin.twice (incr b)) : rfl
  ... = 2 * bin_nat (incr b) : rfl
  ... = 2 * succ (bin_nat b) : bin_to_nat_pres_incr
  ... = succ (bin_nat (bin.twice_one b)) : rfl

-- Exercise: 5 stars, advanced (binary_inverse)
definition nat_bin : nat → bin
| zero := bin.zero
| (succ n) := incr (nat_bin n)

theorem nat_bin_nat_id : ∀ (n : nat), bin_nat (nat_bin n) = n
| zero := rfl
| (succ n) := calc
  bin_nat (nat_bin (succ n)) = bin_nat (incr (nat_bin n)) : rfl
  ... = succ (bin_nat (nat_bin n)) : bin_to_nat_pres_incr
  ... = succ n : nat_bin_nat_id

definition normalize n := nat_bin (bin_nat n)

theorem normalize_idp : ∀ (b : bin), normalize (normalize b) = normalize b := λb, by unfold normalize; rewrite nat_bin_nat_id

-- Exercise: 2 stars, advanced (plus_comm_informal)
-- Exercise: 2 stars, optional (beq_nat_refl_informal)
