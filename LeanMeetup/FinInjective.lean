import Mathlib.Data.Stream.Defs
import Mathlib.Algebra.Ring.BooleanRing

open Stream' (cons take)

@[simp]
theorem Stream'.head_cons :
    head (cons x xs) = x :=
  rfl

@[simp]
theorem Stream'.tail_cons :
    tail (cons x xs) = xs :=
  rfl

def Word := Stream' Bool

def S : Set Word := fun w =>
  ∃ X : Set Word, w ∈ X ∧ X ⊆ (cons 0 '' (cons 1 '' X)) ∪ (cons 1 '' (cons 0 '' X))

theorem iff (w : Word) : 
    w ∈ S ↔ (∀ n, 
      let p := w.take (2*n)
      p.count 1 = p.count 0
    ) := by
  simp only [List.count, List.countP]
  constructor
  · intro h n
    suffices ∀ k,
      List.countP.go (fun x => x == 1) (take (2 * n) w) k
      = List.countP.go (fun x => x == 0) (take (2 * n) w) k 
    from this _
    intro k
    induction' n with n ih generalizing w k
    · rfl 
    · simp [Nat.mul_succ, take, List.countP.go]
      rcases h with ⟨X, hm, h⟩
      have h' (a) := Set.mem_of_subset_of_mem (a:=a) h
      simp only [Set.mem_union, Set.mem_image, exists_exists_and_eq_and] at h' 
      rcases h' _ hm with ⟨y, hmy, ⟨⟩⟩|⟨y, hmy, ⟨⟩⟩
      <;> (
        simp [
          show ((0 : Bool) == 1) = false from rfl,
          show ((1 : Bool) == 0) = false from rfl
        ]
        apply ih _ ⟨X, hmy, h⟩
      )
  · intro h
    use (fun w => ∀ n, 
      let p := w.take (2*n)
      p.count 1 = p.count 0  
    )
    use h
    intro w hw
    simp only [Membership.mem, Set.Mem] at hw  
    simp only [Set.mem_union, Set.mem_image, exists_exists_and_eq_and]
    by_contra hc
    simp [not_or, (· ∈ ·), Set.Mem] at hc
    rcases hc with ⟨hc1, hc2⟩
    let wc : Word := (· % 2 = 0)
    have hwc : ∀ (n : ℕ), List.count 1 (take (2 * n) wc) = List.count 0 (take (2 * n) wc) := by
      intro n
      suffices ∀ b k,
        List.countP.go (fun x => x == b) (take (2 * n) wc) k = (k+n)
      by 
        simp [List.count, List.countP, this]
      intro b k
      induction' n with n ih generalizing k
      · rfl
      · simp [
          Nat.mul_succ, take, List.countP.go, Stream'.head, Stream'.tail, Stream'.nth,
          show ∀i, (i + 1 + 1) % 2 = i % 2 by intro i; simp [show i + 1 + 1 = i + 2 from rfl],
          ih
        ]
        cases b <;> simp [
          show (true == false) = false from rfl,
          show (false == true) = false from rfl,
          Nat.add_assoc k 1 n, Nat.add_comm 1 n
        ]
    specialize hc1 wc hwc
    specialize hc2 wc hwc
    

      