import Mathlib


/--
  `sumOfSequence n` is the sum of the sequence `0, 1, ..., n`
-/
def sumOfSequence : Nat → Nat
  | 0   => 0
  | n+1 => sumOfSequence n + (n+1)

#eval sumOfSequence 0
#eval sumOfSequence 1
#eval sumOfSequence 2
#eval sumOfSequence 3
#eval sumOfSequence 4
#eval sumOfSequence 5
#eval sumOfSequence 6

#check Nat.modCore

@[simp] lemma Nat.one_le_succ (x) : 1 ≤ succ x := by
  exact tsub_add_cancel_iff_le.mp rfl

@[simp] lemma Nat.modCore_one (x) : Nat.modCore x 1 = 0 := by
  induction x <;> (try unfold Nat.modCore; simp [*])

@[simp] lemma Nat.modCore_zero (x) : Nat.modCore 0 x = 0 := by
  unfold Nat.modCore
  simp only [nonpos_iff_eq_zero, ge_iff_le, _root_.zero_le, tsub_eq_zero_of_le, ite_eq_right_iff,
    and_imp]
  rintro _ ⟨⟩; rfl

@[simp]
theorem Nat.ge_mod (n x : ℕ) : (n+1) > (x % (n+1)) := by
  simp [(· % ·), Mod.mod, Nat.mod]
  cases x
  next => simp
  next x =>
    simp
    induction x using Nat.strongInductionOn
    next x ih =>
      unfold Nat.modCore
      cases x <;> simp [Nat.succ_le_succ_iff]
      next =>
        cases n <;> simp
      next x =>
        cases' n with n <;> simp
        split_ifs with h
        · cases hm : x - n
          next => simp
          next =>
            apply ih
            apply Nat.lt_of_succ_le
            apply Nat.le_succ_of_le
            rw [←hm]
            apply sub_le
        · apply Nat.succ_lt_succ_iff.mpr
          apply not_le.mp h

@[simp] lemma not_le_mod (x n) : ¬((n+1) ≤ (x % (n+1))) := by
  simp only [not_le, Nat.ge_mod]



theorem sumOfSequence_eq :
    sumOfSequence n = n * (n + 1) / 2 := by
  simp [Nat.mul_add]
  induction n
  next      => rfl
  next n ih =>
    simp only [sumOfSequence, ih, Nat.add_succ, add_zero, Nat.succ_mul, Nat.mul_succ, Nat.succ_add]
    simp [
      Nat.add_div (b:=2),
      Nat.add_assoc (_+n) n n,
      ←Nat.mul_two n,
      Nat.add_div (b := n*2)
    ]
