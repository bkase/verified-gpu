/-
  Kernel/Examples/Blelloch.lean

  Blelloch-style upsweep/downsweep phases:
    • define the guarded accesses (`tid % (2*off) = 0`)
    • package them as single-phase grades with a trailing barrier
    • discharge WritesDisjointPhase / NoRAWIntraPhase using affine lemmas
    • expose helpers showing how to apply `HasGrade.g_for_threads`
-/
import Kernel.Syntax
import Kernel.Typing
import Kernel.Lemmas.Affine

namespace Kernel
namespace Examples

open Effects
open Kernel.Lemmas
open Kernel.HasGrade
open Grade
open LanguageQuantale

/-- Guard activating threads whose id is a multiple of `2*off`. -/
@[inline] def upsweepGuard (off : Nat) : Guard :=
  { step := 2 * off, phase := 0 }

/-- Workgroup access helper with affine index `tid + shift`. -/
@[inline] def wgBuf (base : String) (shift : Int) (g : Guard) : Access :=
  { space := .workgroup
  , base  := base
  , idx   := { a_tid := 1, a_off := 0, b := shift }
  , guard := g }

/-- Phase for a single upsweep stage (read `tid + off - 1`, write `tid + 2*off - 1`). -/
def upsweepPhase (off : Nat) : Phase :=
  let g := upsweepGuard off
  let r := wgBuf "buf" (Int.ofNat off - 1) g
  let w := wgBuf "buf" (2 * Int.ofNat off - 1) g
  { reads := [r], writes := [w] }

/-- Grade for the upsweep stage: single phase plus a workgroup barrier. -/
def gradeUpsweep (off : Nat) : Grade :=
  Word.ofList [upsweepPhase off] * Grade.ofBarrier

/-- Phase for a single downsweep stage (writes `tid + off - 1` and `tid + 2*off - 1`). -/
def downsweepPhase (off : Nat) : Phase :=
  let g := upsweepGuard off
  let w1 := wgBuf "buf" (Int.ofNat off - 1) g
  let w2 := wgBuf "buf" (2 * Int.ofNat off - 1) g
  { reads := [], writes := [w1, w2] }

/-- Grade for the downsweep stage. -/
def gradeDownsweep (off : Nat) : Grade :=
  Word.ofList [downsweepPhase off] * Grade.ofBarrier

/-- Empty phases are trivially safe. -/
lemma safety_empty_phase :
  WritesDisjointPhase { reads := [], writes := [] } ∧
  NoRAWIntraPhase    { reads := [], writes := [] } := by
  constructor
  · intro i j off a b hij ha hb _ _ _
    simp at ha
  · intro i j off r w hr _ _ _
    simp at hr

/-- Helper: reduce the guard constraint to `i % (2*off) = 0`. -/
lemma guard_mod_eq_zero {off i : Nat}
  (h : i % (upsweepGuard off).step = (upsweepGuard off).phase % (upsweepGuard off).step) :
  i % (2 * off) = 0 := by
  have := h
  simp [upsweepGuard, Nat.zero_mod, Nat.mul_comm] at this
  simpa [Nat.mul_comm] using this

/-- Upsweep writes are pairwise distinct across threads. Guards are unused here. -/
lemma upsweep_WritesDisjoint (off : Nat) :
  WritesDisjointPhase (upsweepPhase off) := by
  intro i j offV a b hij ha hb _ _ _
  have ha' :
      a = wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off) := by
    simpa [upsweepPhase] using ha
  have hb' :
      b = wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off) := by
    simpa [upsweepPhase] using hb
  subst ha'
  subst hb'
  simpa [wgBuf, Aff2.eval] using upsweep_index_distinct off hij

/-- Upsweep phase has no intra-phase RAW hazards when `off > 0`. -/
lemma upsweep_NoRAWIntra (off : Nat) (hoff : 0 < off) :
  NoRAWIntraPhase (upsweepPhase off) := by
  intro i j offV r w hr hw hi hj
  have hr' :
      r = wgBuf "buf" (Int.ofNat off - 1) (upsweepGuard off) := by
    simpa [upsweepPhase] using hr
  have hw' :
      w = wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off) := by
    simpa [upsweepPhase] using hw
  subst hr'
  subst hw'
  have hi0 : i % (2 * off) = 0 := guard_mod_eq_zero hi
  have hj0 : j % (2 * off) = 0 := guard_mod_eq_zero hj
  refine Or.inr ?_
  simpa [wgBuf, Aff2.eval] using
    upsweep_guard_mixed_targets_ne hoff hi0 hj0

/-- Downsweep writes are pairwise distinct (cross-thread) when `off > 0`. -/
lemma downsweep_WritesDisjoint (off : Nat) (hoff : 0 < off) :
  WritesDisjointPhase (downsweepPhase off) := by
  intro i j offV a b hij ha hb _ hi hj
  simp [downsweepPhase] at ha hb
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · subst ha; subst hb
    simpa [wgBuf, Aff2.eval] using (downsweep_index_distinct_both off hij).left
  · subst ha; subst hb
    have hi0 : i % (2 * off) = 0 := guard_mod_eq_zero (by simpa [upsweepGuard] using hi)
    have hj0 : j % (2 * off) = 0 := guard_mod_eq_zero (by simpa [upsweepGuard] using hj)
    simpa [wgBuf, Aff2.eval] using
      upsweep_guard_mixed_targets_ne hoff hi0 hj0
  · subst ha; subst hb
    have hi0 : i % (2 * off) = 0 := guard_mod_eq_zero (by simpa [upsweepGuard] using hi)
    have hj0 : j % (2 * off) = 0 := guard_mod_eq_zero (by simpa [upsweepGuard] using hj)
    have hneq := upsweep_guard_mixed_targets_ne hoff hj0 hi0
    have hswap :
        (Int.ofNat i + (2 * Int.ofNat off - 1))
          ≠ (Int.ofNat j + (Int.ofNat off - 1)) := by
      intro hEq
      exact hneq (by simpa using hEq.symm)
    simpa [wgBuf, Aff2.eval, add_comm, add_left_comm, add_assoc] using hswap
  · subst ha; subst hb
    simpa [wgBuf, Aff2.eval] using (downsweep_index_distinct_both off hij).right

/-- Downsweep has no reads in this phase, so NoRAW is immediate. -/
lemma downsweep_NoRAWIntra (off : Nat) :
  NoRAWIntraPhase (downsweepPhase off) := by
  intro i j offV r w hr _ _ _
  cases hr

/-- Package upsweep safety facts. -/
lemma upsweep_phase_safe (off : Nat) (hoff : 0 < off) :
  WritesDisjointPhase (upsweepPhase off) ∧
  NoRAWIntraPhase (upsweepPhase off) :=
  ⟨upsweep_WritesDisjoint off, upsweep_NoRAWIntra off hoff⟩

/-- Package downsweep safety facts. -/
lemma downsweep_phase_safe (off : Nat) (hoff : 0 < off) :
  WritesDisjointPhase (downsweepPhase off) ∧
  NoRAWIntraPhase (downsweepPhase off) :=
  ⟨downsweep_WritesDisjoint off hoff, downsweep_NoRAWIntra off⟩

/-- Every phase in `gradeUpsweep off` satisfies the DRF side-conditions. -/
lemma gradeUpsweep_safe (off : Nat) (hoff : 0 < off) :
  ∀ p ∈ Grade.phases (gradeUpsweep off),
    WritesDisjointPhase p ∧ NoRAWIntraPhase p := by
  intro p hp
  have hmem :
      p ∈ [upsweepPhase off] ++ (Grade.ofBarrier).toList := by
    simpa [gradeUpsweep, Grade.seq, Grade.phases, Grade.toList_mul] using hp
  rcases List.mem_append.mp hmem with h | h
  · have hp_eq : p = upsweepPhase off := by
      simpa using h
    subst hp_eq
    exact upsweep_phase_safe off hoff
  · have hp_empty : p = ⟨[], []⟩ := by
      simpa [Grade.ofBarrier] using h
    subst hp_empty
    exact safety_empty_phase

/-- Every phase in `gradeDownsweep off` satisfies the DRF side-conditions. -/
lemma gradeDownsweep_safe (off : Nat) (hoff : 0 < off) :
  ∀ p ∈ Grade.phases (gradeDownsweep off),
    WritesDisjointPhase p ∧ NoRAWIntraPhase p := by
  intro p hp
  have hmem :
      p ∈ [downsweepPhase off] ++ (Grade.ofBarrier).toList := by
    simpa [gradeDownsweep, Grade.seq, Grade.phases, Grade.toList_mul] using hp
  rcases List.mem_append.mp hmem with h | h
  · have hp_eq : p = downsweepPhase off := by
      simpa using h
    subst hp_eq
    exact downsweep_phase_safe off hoff
  · have hp_empty : p = ⟨[], []⟩ := by
      simpa [Grade.ofBarrier] using h
    subst hp_empty
    exact safety_empty_phase

/--
If a statement `body` synthesizes `gradeUpsweep off`, we can wrap it in `for_threads`
by citing the affine lemmas proved above.
-/
lemma hasGrade_forThreads_upsweep {Γ : Ctx} {body : Stmt}
  (off : Nat) (hoff : 0 < off)
  (hb : HasGrade Γ body (gradeUpsweep off)) :
  HasGrade Γ (.for_threads body) (gradeUpsweep off) :=
  HasGrade.g_for_threads hb (gradeUpsweep_safe off hoff)

/-- Same story for downsweep stages. -/
lemma hasGrade_forThreads_downsweep {Γ : Ctx} {body : Stmt}
  (off : Nat) (hoff : 0 < off)
  (hb : HasGrade Γ body (gradeDownsweep off)) :
  HasGrade Γ (.for_threads body) (gradeDownsweep off) :=
  HasGrade.g_for_threads hb (gradeDownsweep_safe off hoff)

end Examples
end Kernel
