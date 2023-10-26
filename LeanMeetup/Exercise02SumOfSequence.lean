import Mathlib

/-!
  You can run `lake exe cache get` in your shell to download the built Mathlib files from the cache
-/

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

theorem sumOfSequence_eq :
    sumOfSequence n = n * (n + 1) / 2 := by
  sorry
