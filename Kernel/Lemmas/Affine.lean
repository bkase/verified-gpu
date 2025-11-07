/-
  Kernel/Lemmas/Affine.lean

  Small arithmetic lemmas for discharging Effects.WritesDisjointPhase
  and Effects.NoRAWIntraPhase in Blelloch-like stages.
-/
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Effects

namespace Kernel
namespace Lemmas
open Effects

/-- Adding the same constant on both sides preserves (in)equality over `Int`. -/
lemma add_const_ne {x y c : Int} (h : x ≠ y) : x + c ≠ y + c := by
  intro hsum
  -- cancel the same constant from both sides
  have hxy : x = y := by
    have := congrArg (fun z => z - c) hsum
    -- `(x + c) - c = x`, `(y + c) - c = y`
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact h hxy

/-- A convenient lift: if `i ≠ j` as natural numbers, then their `Int` embeddings differ. -/
lemma int_ofNat_ne {i j : Nat} (h : i ≠ j) : (Int.ofNat i) ≠ (Int.ofNat j) := by
  intro h'
  exact h (Int.ofNat.inj h')

/-- Upsweep write indices are pairwise distinct across distinct threads.
    Index function: `i ↦ i + (2*off) - 1` on `Int`.

    You typically use this with `off : Nat`, `hoff : 0 < off`,
    and guards of the form `tid % (2*off) = 0`, but the guard
    is *not needed* for injectivity—distinct `i ≠ j` suffice.
-/
lemma upsweep_index_distinct
  (off : Nat) :
  ∀ {i j : Nat}, i ≠ j →
    (Int.ofNat i + (2 * (Int.ofNat off) - 1))
      ≠ (Int.ofNat j + (2 * (Int.ofNat off) - 1)) := by
  intro i j hij
  have hij' : (Int.ofNat i) ≠ (Int.ofNat j) := int_ofNat_ne hij
  exact add_const_ne (x := Int.ofNat i) (y := Int.ofNat j)
                     (c := 2 * (Int.ofNat off) - 1) hij'

/-- Downsweep write indices are pairwise distinct across distinct threads
    for BOTH targets:

      idx₁(i) = i + off - 1
      idx₂(i) = i + 2*off - 1
-/
lemma downsweep_index_distinct_both
  (off : Nat) :
  ∀ {i j : Nat}, i ≠ j →
    (Int.ofNat i + (Int.ofNat off - 1)) ≠ (Int.ofNat j + (Int.ofNat off - 1))
  ∧ (Int.ofNat i + (2 * (Int.ofNat off) - 1)) ≠ (Int.ofNat j + (2 * (Int.ofNat off) - 1)) := by
  intro i j hij
  have hij' : (Int.ofNat i) ≠ (Int.ofNat j) := int_ofNat_ne hij
  refine And.intro
    (add_const_ne (x := Int.ofNat i) (y := Int.ofNat j) (c := Int.ofNat off - 1) hij')
    (add_const_ne (x := Int.ofNat i) (y := Int.ofNat j) (c := 2 * (Int.ofNat off) - 1) hij')

/-- Within a single thread, the two downsweep targets differ when `off > 0`:

      i + off - 1  ≠  i + 2*off - 1

    This is useful to rule out intra-thread WAW or RAW at the same address
    inside a downsweep phase.
-/
lemma downsweep_targets_distinct_same_tid
  {i off : Nat} (hoff : 0 < off) :
  (Int.ofNat i + (Int.ofNat off - 1))
    ≠ (Int.ofNat i + (2 * (Int.ofNat off) - 1)) := by
  -- If they were equal, cancel common `(Int.ofNat i) - 1` to get `off = 2*off`.
  intro heq
  have hoffZ : (0 : Int) < Int.ofNat off := Int.natCast_pos.mpr hoff
  have hlt : Int.ofNat off < 2 * Int.ofNat off := by
    linarith [hoffZ]
  have hmul : Int.ofNat off = 2 * Int.ofNat off := by
    have := congrArg (fun z => z + (1 - Int.ofNat i)) heq
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact (ne_of_lt hlt) hmul

/-- Under the upsweep guard (`tid % (2*off) = 0`) with `off > 0`,
    the indices `tid + off - 1` and `tid' + 2*off - 1` cannot coincide. -/
lemma upsweep_guard_mixed_targets_ne
  {i j off : Nat} (hoff : 0 < off)
  (hi : i % (2 * off) = 0) (hj : j % (2 * off) = 0) :
  (Int.ofNat i + (Int.ofNat off - 1))
    ≠ (Int.ofNat j + (2 * (Int.ofNat off) - 1)) := by
  intro hEq
  -- Move the `-1` terms to get a cleaner ℕ equality.
  have hplus := congrArg (fun z => z + 1) hEq
  have hNat :
      i + off = j + 2 * off := by
    have : Int.ofNat (i + off) = Int.ofNat (j + 2 * off) := by
      simpa [Int.natCast_add, two_mul, add_comm, add_left_comm, add_assoc] using hplus
    exact Int.ofNat.inj this
  -- Evaluate both sides modulo `2*off`.
  have hoff_lt : off < 2 * off := by
    have : 1 < 2 := by decide
    simpa [one_mul] using Nat.mul_lt_mul_of_pos_right this hoff
  have hleft :
      (i + off) % (2 * off) = off := by
    have hoff_mod : off % (2 * off) = off := Nat.mod_eq_of_lt hoff_lt
    simpa [Nat.add_mod, hi, hoff_mod, Nat.zero_mod] using
      (Nat.add_mod i off (2 * off))
  have hright :
      (j + 2 * off) % (2 * off) = 0 := by
    have htwo_mod : (2 * off) % (2 * off) = 0 := by
      simp [Nat.mul_comm]
    simpa [Nat.add_mod, hj, htwo_mod, Nat.zero_mod] using
      (Nat.add_mod j (2 * off) (2 * off))
  -- Take both sides of `hNat` modulo `2*off` to reach a contradiction.
  have := congrArg (fun n => n % (2 * off)) hNat
  simp [hleft, hright] at this
  exact (Nat.ne_of_gt hoff) this

/-
  How to use these lemmas in your phase obligations:

  • For upsweep WritesDisjointPhase:
      pick the unique write Access with idx.b = (2*off) - 1 and a_tid = 1;
      for i ≠ j, apply `upsweep_index_distinct off hij`.

  • For downsweep WritesDisjointPhase:
      there are two writes per active thread; for i ≠ j use the two components
      of `downsweep_index_distinct_both off hij` to prove pairwise disjointness
      across threads; within the same thread, use
      `downsweep_targets_distinct_same_tid hoff` to show the two targets differ.

  Guards of the form `tid % (2*off) = 0` restrict *which* threads are active,
  but injectivity does not rely on them; they matter for other shapes of phases
  or when you need to justify that some thread is inactive.
-/

end Lemmas
end Kernel
