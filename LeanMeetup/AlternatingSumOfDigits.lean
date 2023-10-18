import Mathlib

def Digits : Type := List Nat

def toDecimalDigits : Nat → Digits
  | 0 => []
  | x+1 => 
    have : (x+1) / 10 < x +1 := Nat.div_lt_self' ..
    (x + 1) % 10 :: (toDecimalDigits ((x+1) / 10))
termination_by _ x => x

#eval toDecimalDigits 1234567
#eval toDecimalDigits 7654321

def Digits.toNat : Digits → Nat
  | []    => 0
  | x::xs => x + ((toNat xs) * 10)

inductive AddOrSub
  | add
  | sub

def alternatingSum : List Nat → (op : AddOrSub := .add) → Nat
  | [], _ => 0
  | x :: xs, .add => x + alternatingSum xs .sub
  | x :: xs, .sub => x - alternatingSum xs .add



/-!
  ## Lemmas & Theorems
-/

theorem Nat.lt_of_lt_succ_and_neq (h_neq : ¬x = n) (h_lt : x < n + 1) :
    x < n := by
  sorry

lemma Nat.succ_mod :
    (x+1) % (n+1) = if x % (n+1) = n then 0 else (x % (n+1)) + 1 := by
  induction' x with x ih
  · simp
    cases n <;> rfl
  · simp [add_mod, ih]
    split_ifs <;> simp_all
    · cases n
      · contradiction
      · apply one_lt_succ_succ
    · repeat
        apply lt_of_lt_succ_and_neq
        · simp; assumption
        apply succ_lt_succ
      apply Nat.mod_lt _ (succ_pos _)

lemma Nat.div_mul :
    (x / 10 * 10) = x - (x % 10) := by
  induction' x with x ih
  · rfl
  · simp [succ_div, add_mul, ih, dvd_iff_mod_eq_zero, 
      show succ x = x + 1 from rfl,
      succ_mod
    ]
    split_ifs <;> simp_all
    · apply Nat.sub_add_cancel
      rcases x with ⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|⟨⟩|x
      <;> try contradiction
      repeat apply succ_lt_succ
      apply succ_pos

@[simp] theorem div_mul_add_mod (x : Nat) :
    (x / 10 * 10) + (x % 10) = x := by
  rw [Nat.div_mul, Nat.sub_add_cancel]
  exact Nat.mod_le x _

@[simp] theorem toDecimalDigits_toNat :
    (toDecimalDigits x |>.toNat) = x := by
  induction' x using Nat.strongInductionOn with x ih
  cases' x with x
  · rfl 
  · rw [toDecimalDigits, Digits.toNat, ih ((x+1) / 10)]
    · rw [Nat.add_comm, div_mul_add_mod]
    · apply Nat.div_lt_self'

#check List.head

def Digits.isMinimal (xs : Digits) : Prop :=
  (List.getLast? xs ≠ some 0)

theorem Digits.toNat_cons (xs : Digits) (h : xs.isMinimal) :
    xs.toNat ≠ 0 := by
  sorry

@[simp] theorem toNat_toDecimalDigits (x : Digits) :
    toDecimalDigits x.toNat = x := by
  induction' x with x xs ih
  · rfl
  · simp [Digits.toNat, toDecimalDigits]


theorem dvd_eleven_iff_alternatingSum_digits_dvd_eleven (x : Nat) :
    11 ∣ x ↔ 11 ∣ (alternatingSum <| toDecimalDigits x) := by
  simp [Nat.dvd_iff_mod_eq_zero, toDecimalDigits]
  induction' x using Nat.strongInductionOn with x ih
  · unfold toDecimalDigits
    simp only
    split
    next => simp only
    next x =>
      simp
      conv_rhs => rw [←decompose x]
      simp
  