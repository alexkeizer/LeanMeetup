
namespace LeanDemo

/-!

  # Lean Meetup Demo: Lean 101

  Let's define the natural numbers in Lean!
  We will do this in the style of the Peano axioms.

  That is, following the pen and paper definition of
    * `0` is a natural number
    * If `x` is a natural number, then the successor of `x` (i.e., `x + 1`) is also a natural number
    * Nothing else is a natural number

  In maths, we would talk about the **set** of natural numbers.
  Lean, however, has as type theory as its foundation, so we generally talk about **types**. 

  So without further ado, here is the definition 

-/
--     /-- We are defining an **inductive type**
--    /
--   /      /-- `Nat` is the name of the type being defined
--  /\     /
inductive Nat where
  | zero : Nat            -- `zero` is a `Nat`
  | succ (n : Nat) : Nat  -- if `n` is a `Nat`, then `succ n` is a `Nat`

/-!
  We call `zero` and `succ` the **constructors** of `Nat`, and they correspond to the first two
  bullet-points in our pen-and-paper definition.
  The last bullet-point, that that nothing else is a natural number, 
  is implicit in the definition of an inductive type.
-/

#check Nat
#check Nat.zero
#check Nat.succ


/- `open Nat` means that `Nat.zero` and `Nat.succ` can now be referred to as 
    `zero` and `succ`, respectively -/
open Nat

/-!
  ## Notation
  It's kind of tedious to write `succ (succ zero)` everytime we mean `2`, so we define a bit of
  notation for numerals. Don't worry too much about how this works.
-/
instance : OfNat Nat (nat_lit 0) := ⟨zero⟩    -- `0` is `zero`
instance : OfNat Nat (nat_lit 1) := ⟨succ 0⟩  -- `1` is `succ 0`
instance : OfNat Nat (nat_lit 2) := ⟨succ 1⟩  -- `2` is `succ 1`
instance : OfNat Nat (nat_lit 3) := ⟨succ 2⟩  -- `3` is `succ 2`



/-!
  Now that we have this notation, let's proof I didn't mess anything up!
-/

--    /-- We're proving a theorem!
--   /
--  /        /-- The name of our theorem is `zero_eq`
-- /\       /\
theorem zero_eq :
    0 = zero := by    -- The statement we are proving is `0 = zero`, then `:= by` starts the proof
  rfl                 -- `rfl` is a **tactic** which proves thing that are true by definition

theorem one_eq_succ_zero :
    1 = succ 0 := by
  rfl

theorem two_eq_succ_one :
    2 = succ 1 := by
  rfl

theorem three_eq_succ_two :
    3 = succ 2 := by
  rfl


/-!
  Now let's proof that `3` is equal to `succ (succ (succ (zero)))`
-/

theorem three_eq_succ_succ_succ_zero :
    3 = succ (succ (succ zero)) := by
  -- `rfl` would still work!
  rw [three_eq_succ_two]  -- `rw` is another tactic that substitutes a given equality
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rw [zero_eq]




/-!
  ## Addition
-/

--     /-- We are giving a **definition**
--    /
--   /   /-- The name of our definition is `add`
--  /   /
-- /   /    /-- If `x` and `y` are `Nat`s, then `add x y` is a `Nat`
--/   /    /    That is, `add` is a function which takes two `Nat`s as argument, and returns a `Nat`
def add : Nat → Nat → Nat 
  | x, 0      => x              -- `x + 0` is defined as `x`
  | x, succ y => succ (add x y) -- `x + (succ y)` is `succ (x + y)`


-- More notation, we write `x + y` to mean `add x y`.
instance : Add Nat := ⟨add⟩



/-!
  Theorems about addition
-/

/-- `x + 0` is equal to `x`, for all natural numbers `x` -/
theorem add_zero : 
    ∀ (x : Nat), x + 0 = x := by
  intro x     -- introduce the universally quantified variable `x`
  rfl

/-- `x + (succ y)` is equal to `succ (x + y)`, for all natural numbers `x` and `y` -/
theorem add_succ :
    ∀ (x y : Nat), x + (succ y) = succ (x + y) := by
  intro x y
  rfl


theorem zero_add :
    ∀ (x : Nat), 0 + x = x := by
  --
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  -- 
  --
  --
  intro x
  -- New tactic! **induction** does a case split on `x` and generates an induction hypothesis
  induction x 

  -- Suppose that `x = 0`
  case zero         => 
    rfl

  -- Otherwise, `x` must be `succ x'` for some `x'`
  -- We also get an induction hypothesis `ih : 0 + x' = x'` 
  case succ x' ih   => 
    rw [add_succ, ih]    -- `rw [a, b]` is the same as `rw [a]`, then `rw [b]`


























end LeanDemo