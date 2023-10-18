
namespace LeanDemo

set_option autoImplicit false

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

-/
--     /-- We are defining an **inductive type**
--    /
--   /      /-- `Nat` is the name of the type being defined
--  /      /
inductive Nat where
  | zero : Nat            -- `zero` is a `Nat`
  | succ (n : Nat) : Nat  -- if `n` is a `Nat`, then `succ n` is a `Nat`

/-!
  `:` is the type-equivalent of `∈`, and is usually read as "is a".
  `x : α` means that `x` is of type `α`.

  ## Constructors
  We call `zero` and `succ` the **constructors** of `Nat`, and they correspond to the first two
  bullet-points in our pen-and-paper definition.
  The last bullet-point, that nothing else is a natural number, is implicit in the definition of an inductive type.

  The `inductive` command has added three definitions to the environment, 
  one for the type itself `Nat`, and one for each constructor.
  We can use the `#check` command to check the types
-/

#check Nat      -- `LeanDemo.Nat : Type`
#check Nat.zero -- `LeanDemo.Nat.zero : Nat`
#check Nat.succ -- `LeanDemo.Nat.succ (n : Nat) : Nat`


/- `open Nat` means that `Nat.zero` and `Nat.succ` can now be referred to as `zero` and `succ`, respectively -/
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
  ## Theorems and Tactics

  In Lean, we define a theorem as follows:
  ```
  theorem [name_of_theorem] :
      [statement_of_theorem] := by
    [proof]
  ```

  The name of a theorem is just an identifier allowing us to refer to it in later results.
  The statement of the theorem is the actual thing we are trying to proof. 
  For example, `1 + 0 = 1` could be the statement of a theorem.

  The word `by` indicates that we are starting a proof in **tactic mode**.
  Lean will give us an interactive info-view showing the current proof state,
  including the **goals** we are trying to proof.
  The goal will initially be just the statement of the theorem.
  In the proof, we write tactics to either
    * Prove the goal directly, closing it, or
    * Transform the goal into a simpler goal, which we can then prove with further tactics

  `rfl` (short for *reflexive*) is the first tactic we will see. It can prove goals of the form `x = y`, where
    `x` and `y` are "definitionally equal".
    Generally, that means `rfl` can prove the goal if the equality is true by definition

  Let's see some examples, where we prove the notation I defined indeed uses `zero` and `succ` correctly
-/

--    /-- We're proving a theorem!
--   /
--  /        /-- The name of our theorem is `zero_eq`
-- /        /
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
  Now let's proof that `3` is equal to `succ (succ (succ (zero)))`.

  We could use `rfl` again, it can see through multiple definitions.
  However, I want to show another tactic.

  `rw [h]` (short for *rewrite*) takes an equality `h : a = b` as argument, and replaces occurences 
    of `a` in the goal with `b`. If the resulting goal is sufficiently simple, `rw` closes (proves) 
    the goal
-/

theorem three_eq_succ_succ_succ_zero :
    3 = succ (succ (succ zero)) := by
  rw [three_eq_succ_two]
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rw [zero_eq]

/-!
  Note that we can also give `rw` multiple, comma-separeted, equalities at the same time, 
-/

theorem three_eq_succ_succ_succ_zero' :
    3 = succ (succ (succ zero)) := by
  rw [three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero, zero_eq]



/-!
  ## Addition
  Now let us define what it means to add two natural numbers together!
  The syntax should be somewhat familiar if you've done any functional programing.
  If not, don't worry about the syntax too much!

  Essentially, we are defining `add` as a function that takes two `Nat`s as argument, and returns
  a third `Nat`. In Lean, we spell the type of such functions as `Nat → Nat → Nat`.
  Note that `→` is right-associative, so the above type is the same as `Nat → (Nat → Nat)`.

  Then, we define `add` **recursively**, by doing a case-distinction on the second argument.
  That is, if the second argument is `0`, then we define `x + 0 = x`.
  If the second argument is instead `succ y`, then we are allowed to assume that `x + y` is
  already defined, and indeed use that to define `x + (succ y) = succ (x + y)`.
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
  Let's prove some theorems about addition!
  We want to prove statements about arbitrary natural numbers `x`. 
  The syntax for this is `∀ (x : Nat), ...`, and the corresponding tactic is

  `intro x`
    If the goal is `⊢ ∀ (y : α), P y`, then `intro x` will move the universally quantified
    variable into the local context, renaming all occurences of `y` to the given name `x` and
    transforming the goal into `x : α ⊢ P x`
-/

/-- `x + 0` is equal to `x`, for all natural numbers `x` -/
theorem add_zero : 
    ∀ (x : Nat), x + 0 = x := by
  intro y     -- introduce the universally quantified variable `x`
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
  /-
    `induction x`
      Given a natural number `x`, the `induction` tactic will split a goal `⊢ P x` into two goals:
      * the base case `⊢ P 0`, and
      * the recursive step `ih : P x ⊢ P (succ x)`

    `case zero => ...` 
      focusses on the goal named `zero` (i.e., the base case)

    `case succ x' ih => ...`
      focusses on the goal names `succ` (i.e., the recursive step), 
      uses `x'` as the name for the natural number that `x` is a successor of, and 
      uses `ih` as the name of the induction hypothesis
  -/
  intro x
  induction x 
  -- Suppose that `x = 0`
  case zero         => 
    rfl
  -- Otherwise, `x` must be `succ x'` for some `x'`
  -- We also get an induction hypothesis `ih : 0 + x' = x'` 
  case succ x' ih   =>
    rw [add_succ, ih]





/-
  We can also put universally quantified variables before the `:`, directly after the theorem name.
  This has the same meaning, but does not require us to `intro` the quantified variables, they
  get put in the local context directly
-/
theorem succ_add (x y : Nat) :
    (succ x) + y = succ (x + y) := by
  induction y
  case zero =>      rfl
  case succ y ih => rw [add_succ, add_succ, ih]

-- We can use `#check` to show that `succ_add` indeed proves
--    `∀ (x y : Nat), (succ x) + y = succ (x + y)`
#check succ_add


/-!
  We are now ready to prove the commutativity of addition

  `rw [←h]`: given an equality `h : a = b`, `rw [←h]` rewrites in the opposite direction.
    That is, it replaces occurences of the right-hand-side `b` in the goal with `a`

  `sorry` will "prove" any goal. This has the effect of assuming the truth of that goal as an
    axiom and it is generally used to indicate a "hole" in a proof that you intend to finish later
-/      
theorem add_comm (x y : Nat) : 
    x + y = y + x := by
  induction y
  case zero =>
    rw [←zero_eq, zero_add, add_zero]
  case succ y ih =>
    sorry

/-!
  And associativity
-/
theorem add_assoc (x y z : Nat) :
    (x + y) + z = x + (y + z) := by
  sorry
  












/-!
  # Now it's your turn!

  You can find this file at:
    https://github.com/alexkeizer/LeanMeetup/blob/main/LeanMeetup/Demo01.lean

  * https://adam.math.hhu.de/#/g/hhu-adam/NNG4
  * https://github.com/PatrickMassot/GlimpseOfLean/tree/master

-/












end LeanDemo