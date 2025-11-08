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
  NoRAWIntraPhase    { reads := [], writes := [] } :=
  Kernel.emptyPhase_safe

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
    have hneq :
        (Int.ofNat i + (2 * Int.ofNat off - 1))
          ≠ (Int.ofNat j + (Int.ofNat off - 1)) :=
      upsweep_guard_mixed_targets_ne_sym hoff hi0 hj0
    simpa [wgBuf, Aff2.eval, add_comm, add_left_comm, add_assoc] using hneq
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
  PhasesSafe (gradeUpsweep off) := by
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
  PhasesSafe (gradeDownsweep off) := by
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

/-! ## Workgroup-level composition ------------------------------------------- -/

namespace WG

open Grade
open Kernel.HasGrade

/-- Sequential upsweep grade across a list of offsets. -/
def gradeUpsweeps : List Nat → Grade
| []      => Grade.eps
| o :: os => Grade.seq (gradeUpsweep o) (gradeUpsweeps os)

/-- Sequential downsweep grade across a list of offsets (processed right-to-left). -/
def gradeDownsweeps : List Nat → Grade
| []      => Grade.eps
| o :: os => Grade.seq (gradeDownsweeps os) (gradeDownsweep o)

/-- Full workgroup scan grade: upsweep stages followed by downsweep stages. -/
def wgScanGrade (offs : List Nat) : Grade :=
  Grade.seq (gradeUpsweeps offs) (gradeDownsweeps offs)

/-- All offsets are strictly positive (the Blelloch arithmetic lemmas assume this). -/
def AllPos (offs : List Nat) : Prop := ∀ o ∈ offs, 0 < o

lemma gradeUpsweeps_safe {offs : List Nat}
  (Hall : AllPos offs) :
  PhasesSafe (gradeUpsweeps offs) := by
  induction offs with
  | nil =>
      simpa [gradeUpsweeps] using PhasesSafe.eps
  | cons o os ih =>
      have ho : 0 < o := Hall o (by simp)
      have hrest : AllPos os := by
        intro k hk
        exact Hall k (by simp [hk])
      have hhead := gradeUpsweep_safe o ho
      have htail := ih hrest
      simpa [gradeUpsweeps] using PhasesSafe.seq hhead htail

lemma gradeDownsweeps_safe {offs : List Nat}
  (Hall : AllPos offs) :
  PhasesSafe (gradeDownsweeps offs) := by
  induction offs with
  | nil =>
      simpa [gradeDownsweeps] using PhasesSafe.eps
  | cons o os ih =>
      have ho : 0 < o := Hall o (by simp)
      have hrest : AllPos os := by
        intro k hk
        exact Hall k (by simp [hk])
      have htail := ih hrest
      have hhead := gradeDownsweep_safe o ho
      simpa [gradeDownsweeps] using PhasesSafe.seq htail hhead

/-- The abstract downsweep chain ends with the explicit barrier whenever nonempty. -/
lemma gradeDownsweeps_endsWith_barrier :
  ∀ offs : List Nat, offs ≠ [] →
    ∃ xs0 : List Effects.Phase,
      ((gradeDownsweeps offs : Effects.Grade) : List Effects.Phase)
        = xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
| [], hne => False.elim (hne rfl)
| [o], _ => by
    refine ⟨[downsweepPhase o], ?_⟩
    simp [ gradeDownsweeps
     , Grade.seq
     , Grade.eps
     , gradeDownsweep
     , Grade.ofBarrier
     , LanguageQuantale.Word.toList_mul
     , List.nil_append ]
| o :: o' :: os, _ => by
    -- tail (o' :: os) already ends with the barrier
    rcases gradeDownsweeps_endsWith_barrier (o' :: os) (by simp) with ⟨xs, hx⟩

    -- shape of the abstract tail `(o' :: os)`
    have shape :
      ((gradeDownsweeps (o' :: os)) : List _)
        = ((gradeDownsweeps os : Effects.Grade) : List _)
            ++ [downsweepPhase o'] ++ [⟨[], []⟩, ⟨[], []⟩] := by
      simp [ gradeDownsweeps
           , Grade.seq
           , gradeDownsweep
           , Grade.ofBarrier
           , List.append_assoc ]

    -- same equality as `shape`, but with the `hx` rhs
    have hx' :
      ((gradeDownsweeps (o' :: os)) : List _)
        = xs ++ [⟨[], []⟩, ⟨[], []⟩] := by
      simpa using hx

    -- base equality: prefix-with-barrier = xs-with-barrier
    have base :
      ((gradeDownsweeps os : Effects.Grade) : List _)
        ++ [downsweepPhase o'] ++ [⟨[],[]⟩,⟨[],[]⟩]
      = xs ++ [⟨[],[]⟩,⟨[],[]⟩] :=
      shape.symm.trans hx'

    -- append the same tail `[downsweepPhase o] ++ barrier` to both sides
    have tailApp :
      (((gradeDownsweeps os : Effects.Grade) : List _)
          ++ [downsweepPhase o'] ++ [⟨[],[]⟩,⟨[],[]⟩])
        ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]
      =
      (xs ++ [⟨[],[]⟩,⟨[],[]⟩])
        ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] :=
      congrArg (fun l => l ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]) base

    -- choose the witness that *keeps* the tail barrier then adds this stage
    refine ⟨xs ++ [⟨[],[]⟩,⟨[],[]⟩] ++ [downsweepPhase o], ?_⟩

    -- rewrite the target using definitions + `hx`, and discharge with `tailApp`
    simpa [ gradeDownsweeps
          , Grade.seq
          , gradeDownsweep
          , Grade.ofBarrier
          , hx
          , List.append_assoc ]
      using tailApp

/-- Combined safety for the entire scan grade. -/
lemma wgScanGrade_safe {offs : List Nat}
  (Hall : AllPos offs) :
  PhasesSafe (wgScanGrade offs) := by
  have hUp := gradeUpsweeps_safe (offs := offs) Hall
  have hDown := gradeDownsweeps_safe (offs := offs) Hall
  simpa [wgScanGrade] using PhasesSafe.seq hUp hDown

/-- Once a body synthesizes the composed grade, wrap it under `for_threads`. -/
lemma hasGrade_forThreads_wgScan {Γ : Ctx} {body : Stmt}
  {offs : List Nat} (Hall : AllPos offs)
  (hb : HasGrade Γ body (wgScanGrade offs)) :
  HasGrade Γ (.for_threads body) (wgScanGrade offs) :=
  HasGrade.g_for_threads hb (wgScanGrade_safe Hall)

/-- Upsweeps end with the explicit barrier whenever nonempty (abstract spec). -/
lemma gradeUpsweeps_endsWith_barrier :
  ∀ offs : List Nat, offs ≠ [] →
    ∃ xs0 : List Effects.Phase,
      ((gradeUpsweeps offs : Effects.Grade) : List Effects.Phase)
        = xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
| [], h => False.elim (h rfl)
| [o], _ =>
  by
    refine ⟨[upsweepPhase o], ?_⟩
    simp [gradeUpsweeps, gradeUpsweep, Grade.seq, Grade.ofBarrier, Grade.eps]
| o :: o' :: os, _ =>
  by
    -- split the chain at the head stage
    have hsplit :
      (gradeUpsweeps (o :: o' :: os)).toList
        = (gradeUpsweep o).toList ++ (gradeUpsweeps (o' :: os)).toList := by
      simp [gradeUpsweeps, Grade.seq]

    -- tail ends-with-barrier witness
    rcases gradeUpsweeps_endsWith_barrier (o' :: os) (by simp) with ⟨xs0, hx⟩

    -- choose a witness that carries the head chunk
    refine ⟨(gradeUpsweep o).toList ++ xs0, ?_⟩

    -- plug both equalities; associativity finishes it
    simp [hsplit, hx, List.append_assoc]

/-- List-level: abstract upsweeps are a fixed point of `normalizeList`. -/
lemma gradeUpsweeps_normal_list (offs : List Nat) :
  Effects.Grade.normalizeList
      ((gradeUpsweeps offs : Effects.Grade) : List Effects.Phase)
    = ((gradeUpsweeps offs : Effects.Grade) : List Effects.Phase) := by
  induction offs with
  | nil =>
      simp [gradeUpsweeps, Grade.eps, Grade.normalizeList]
  | cons o os ih =>
      cases os with
      | nil =>
          have hup : (upsweepPhase o).empty = false := by
            simp [upsweepPhase, Effects.Phase.empty]
          -- Use the single-nonempty+barrier lemma, then rewrite [r, B, B] ↔ [r] ++ [B,B]
          have hfix :
            Effects.Grade.normalizeList ([upsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩])
              = [upsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] :=
            Effects.Grade.normalizeList_single_nonempty_barrier _ hup
          simpa [ Effects.Grade.list_singleton_append  -- [r] ++ xs = r :: xs
                , gradeUpsweeps
                , Grade.seq
                , gradeUpsweep
                , Grade.ofBarrier
                , Grade.eps
                , List.nil_append
                ] using hfix
      | cons o' os' =>
          rcases gradeUpsweeps_endsWith_barrier (o' :: os') (by simp) with ⟨xs, hx⟩
          -- coerce hx to list view
          have hxList :
            ((gradeUpsweeps (o' :: os')) : List Effects.Phase)
              = xs ++ [⟨[],[]⟩,⟨[],[]⟩] := by
            simpa using hx
          -- raw head split:
          have shape0 :
            ((gradeUpsweeps (o :: o' :: os')) : List Effects.Phase)
              = ([upsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩])
                  ++ ((gradeUpsweeps (o' :: os')) : List Effects.Phase) := by
            simp [gradeUpsweeps, Grade.seq, gradeUpsweep, Grade.ofBarrier]
          -- plug hx into the tail:
          have shape :
            ((gradeUpsweeps (o :: o' :: os')) : List Effects.Phase)
              = [upsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]
                  ++ (xs ++ [⟨[],[]⟩,⟨[],[]⟩]) := by
            simpa [hxList, List.append_assoc] using shape0
          -- now you can continue with the middle-barrier cut etc.
          -- e.g., something like:
          have hup : (upsweepPhase o).empty = false := by
            simp [upsweepPhase, Effects.Phase.empty]
          calc
            _ = _ := rfl
            _ = Effects.Grade.normalizeList
                    ([upsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]
                      ++ (xs ++ [⟨[],[]⟩,⟨[],[]⟩])) := by
                  simp [shape]
            _ = Effects.Grade.normalizeList [upsweepPhase o]
                  ++ [⟨[],[]⟩,⟨[],[]⟩]
                  ++ Effects.Grade.normalizeList (xs ++ [⟨[],[]⟩,⟨[],[]⟩]) := by
                simpa [List.append_assoc] using
                  Effects.Grade.normalizeList_barrier_middle_append
                    ([upsweepPhase o]) (xs ++ [⟨[],[]⟩,⟨[],[]⟩])
            _ = [upsweepPhase o]
                  ++ [⟨[],[]⟩,⟨[],[]⟩]
                  ++ (Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩]) := by
                simp [ Effects.Grade.normalizeList_single_nonempty, hup
                     , Effects.Grade.normalizeList_append_barrier_right ]
            _ = ((gradeUpsweep o : Effects.Grade) : List _)
                  ++ ((gradeUpsweeps (o' :: os') : Effects.Grade) : List _) := by
              -- from `hx` and `ih`: pack the tail back
              have tailPacked :
                Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩]
                  = ((gradeUpsweeps (o' :: os')) : List _) := by
                -- 1) move from lhs form to normalizeList (xs ++ B)
                have pack1 :
                  Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩]
                    = Effects.Grade.normalizeList (xs ++ [⟨[],[]⟩,⟨[],[]⟩]) :=
                  (Effects.Grade.normalizeList_append_barrier_right xs).symm
                -- 2) rewrite (xs ++ B) to the tail via hx
                have pack2 :
                  Effects.Grade.normalizeList (xs ++ [⟨[],[]⟩,⟨[],[]⟩])
                    = Effects.Grade.normalizeList ((gradeUpsweeps (o' :: os')).toList) :=
                  (congrArg Effects.Grade.normalizeList hx).symm
                -- 3) fold the normalized tail back to its raw list via the IH on (o' :: os')
                exact pack1.trans (pack2.trans ih)
              simp [gradeUpsweep, Grade.ofBarrier, tailPacked]
            _ = ((gradeUpsweeps (o :: o' :: os')) : List _) := by
              simp [gradeUpsweeps, Grade.seq]

/-- List-level: abstract downsweeps are a fixed point of `normalizeList`. -/
lemma gradeDownsweeps_normal_list (offs : List Nat) :
  Effects.Grade.normalizeList
      ((gradeDownsweeps offs : Effects.Grade) : List Effects.Phase)
    = ((gradeDownsweeps offs : Effects.Grade) : List Effects.Phase) := by
  induction offs with
  | nil =>
      simp [gradeDownsweeps, Grade.eps, Grade.normalizeList]
  | cons o os ih =>
      cases os with
      | nil =>
          have hdn : (downsweepPhase o).empty = false := by
            simp [downsweepPhase, Effects.Phase.empty]
          -- build the fixed-point fact in append form:
          have hfix :
            Effects.Grade.normalizeList ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩])
              = [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] :=
            Effects.Grade.normalizeList_single_nonempty_barrier _ hdn
          -- now rewrite your goal to that shape and apply it
          simpa [ gradeDownsweeps
                , Grade.seq
                , gradeDownsweep
                , Grade.ofBarrier
                , Grade.eps
                , List.nil_append
                , Effects.Grade.list_singleton_append  -- [r] ++ xs = r :: xs
                ] using hfix
      | cons o' os' =>
          rcases gradeDownsweeps_endsWith_barrier (o' :: os') (by simp) with ⟨xs, hx⟩

          -- coerce hx to a plain list equality (no .toList on the LHS)
          have hxList :
            ((gradeDownsweeps (o' :: os')) : List Effects.Phase)
              = xs ++ [⟨[],[]⟩,⟨[],[]⟩] := by
            simpa using hx

          -- HEAD split for the whole list (o :: o' :: os'):
          have headSplit :
            ((gradeDownsweeps (o :: o' :: os')) : List Effects.Phase)
              = ((gradeDownsweeps (o' :: os')) : List Effects.Phase)
                  ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] := by
            simp [gradeDownsweeps, Grade.seq, gradeDownsweep, Grade.ofBarrier, List.append_assoc]

          -- Plug hxList into the tail:
          have shape :
            ((gradeDownsweeps (o :: o' :: os')) : List Effects.Phase)
              = (xs ++ [⟨[],[]⟩,⟨[],[]⟩])
                  ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] := by
            simpa [hxList, List.append_assoc] using headSplit

          have hdn : (downsweepPhase o).empty = false := by
            simp [downsweepPhase, Effects.Phase.empty, wgBuf]

          -- Pack the left chunk back to the abstract tail using hx and ih:
          --   normalizeList xs ++ barrier = (gradeDownsweeps (o' :: os')).toList
          have packLeft :
            Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩]
              = ((gradeDownsweeps (o' :: os')) : List _) := by
            --  normalizeList xs ++ B = normalizeList (xs ++ B)
            have pack1 :
              Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩]
                = Effects.Grade.normalizeList (xs ++ [⟨[],[]⟩,⟨[],[]⟩]) :=
              (Effects.Grade.normalizeList_append_barrier_right xs).symm
            --  normalizeList (xs ++ B) = normalizeList (tail)  by hxList
            have pack2 :
              Effects.Grade.normalizeList (xs ++ [⟨[],[]⟩,⟨[],[]⟩])
                = Effects.Grade.normalizeList ((gradeDownsweeps (o' :: os')).toList) :=
              (congrArg Effects.Grade.normalizeList hxList).symm
            --  normalizeList (tail) = tail  by IH
            exact pack1.trans (pack2.trans ih)
            
          -- (a) collapse the right chunk under the left append
          have rightFix :
            Effects.Grade.normalizeList ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩])
              = [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] :=
            Effects.Grade.normalizeList_single_nonempty_barrier _ hdn

          have stepR :
            (Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩])
              ++ Effects.Grade.normalizeList ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩])
            =
            (Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩])
              ++ ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]) := by
            -- just rewrite the right summand via the fixed-point lemma
            have rightFix :
              Effects.Grade.normalizeList ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩])
                = [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] :=
              Effects.Grade.normalizeList_single_nonempty_barrier _ hdn
            -- map it through the left-append context
            exact
              (congrArg
                (fun tail =>
                  (Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩]) ++ tail)
                rightFix)

          -- Now run the normalizeList calculation for the whole (o :: o' :: os') tail:
          calc
            Effects.Grade.normalizeList
              ((gradeDownsweeps (o :: o' :: os')) : List _)
                = Effects.Grade.normalizeList
                    ((xs ++ [⟨[],[]⟩,⟨[],[]⟩])
                      ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]) := by
                  simp [shape, List.append_assoc]
            _ = Effects.Grade.normalizeList xs
                  ++ [⟨[],[]⟩,⟨[],[]⟩]
                  ++ Effects.Grade.normalizeList ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]) := by
                simpa [List.append_assoc] using
                  Effects.Grade.normalizeList_barrier_middle_append
                    xs ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩])
            -- use these two equalities in the calc:
            _ =
              (Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩])
                ++ ([downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩]) := by exact stepR
            _ =
              (Effects.Grade.normalizeList xs ++ [⟨[],[]⟩,⟨[],[]⟩])
                ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] := by simp [List.append_assoc]
            _ = ((gradeDownsweeps (o' :: os')) : List _)
                  ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] := by
                  simp [packLeft, List.append_assoc]
            _ = ((gradeDownsweeps (o :: o' :: os')) : List _) := by
                  simp [gradeDownsweeps, Grade.seq, gradeDownsweep, Grade.ofBarrier, List.append_assoc]

/-- Spec full scan is a fixed point of `normalize`. -/
@[simp] lemma wgScanGrade_normal (offs : List Nat) :
  Effects.Grade.normalize (wgScanGrade offs) = wgScanGrade offs := by
  -- Prove as lists then rewrap
  apply LanguageQuantale.Word.ext
  cases offs with
  | nil =>
      -- prove list equality and finish with Word.ext
      simp [ wgScanGrade
          , gradeUpsweeps, gradeDownsweeps
          , Grade.seq, Grade.eps
          ]
  | cons o os =>
      -- use a barrier cut at the join; both halves are fixed points listwise
      rcases gradeUpsweeps_endsWith_barrier (o :: os) (by simp) with ⟨xsU, hxU⟩
      have :
        ((Effects.Grade.normalize (wgScanGrade (o :: os))) : List _) =
          Effects.Grade.normalizeList ((wgScanGrade (o :: os)).toList) := by
        exact Effects.Grade.toList_normalize (wgScanGrade (o :: os))
      have joinList :
        ((wgScanGrade (o :: os)) : List Effects.Phase)
          = ((WG.gradeUpsweeps (o :: os)) : List Effects.Phase)
              ++ ((WG.gradeDownsweeps (o :: os)) : List Effects.Phase) := by
        -- wgScanGrade (o::os) = gradeUpsweeps (o::os) * gradeDownsweeps (o::os)
        -- then toList_mul turns * into ++ on lists
        simp [WG.wgScanGrade, Grade.seq, LanguageQuantale.Word.toList_mul]
        -- alternatively: simp [WG.wgScanGrade, Grade.seq, Effects.Grade.toList_mul]
      calc
        ((Effects.Grade.normalize (wgScanGrade (o :: os))) : List _)
            = Effects.Grade.normalizeList
                ((gradeUpsweeps (o :: os) : List _)
                ++ (gradeDownsweeps (o :: os) : List _)) := by
                simp [joinList]
      _ = Effects.Grade.normalizeList xsU
            ++ [⟨[],[]⟩,⟨[],[]⟩]
            ++ Effects.Grade.normalizeList ((gradeDownsweeps (o :: os) : List _)) := by
            -- cut at the upsweep barrier
            simpa [hxU, List.append_assoc] using
              Effects.Grade.normalizeList_barrier_middle_append xsU
                ((gradeDownsweeps (o :: os) : List _))
      _ = ((gradeUpsweeps (o :: os) : List _)
            ++ (gradeDownsweeps (o :: os) : List _)) := by
            -- pack both halves back with the two fixed-point lemmas
            -- pack the left chunk back to abstract upsweeps
            have leftPacked :
              Effects.Grade.normalizeList xsU ++ [⟨[],[]⟩,⟨[],[]⟩]
                = ((WG.gradeUpsweeps (o :: os)) : List Effects.Phase) := by
              -- 1) normalizeList xsU ++ B = normalizeList (xsU ++ B)
              have pack1 :
                Effects.Grade.normalizeList xsU ++ [⟨[],[]⟩,⟨[],[]⟩]
                  = Effects.Grade.normalizeList (xsU ++ [⟨[],[]⟩,⟨[],[]⟩]) :=
                (Effects.Grade.normalizeList_append_barrier_right xsU).symm
              -- 2) rewrite xsU ++ B to the upsweep list using hxU
              have pack2 :
                Effects.Grade.normalizeList (xsU ++ [⟨[],[]⟩,⟨[],[]⟩])
                  = Effects.Grade.normalizeList ((WG.gradeUpsweeps (o :: os)) : List _) :=
                (congrArg Effects.Grade.normalizeList hxU).symm
              -- 3) upsweeps are a fixed point listwise
              have pack3 :
                Effects.Grade.normalizeList ((WG.gradeUpsweeps (o :: os)) : List _)
                  = ((WG.gradeUpsweeps (o :: os)) : List _) :=
                gradeUpsweeps_normal_list (o :: os)
              exact pack1.trans (pack2.trans pack3)
            have rightNorm :
              Effects.Grade.normalizeList
                ((gradeDownsweeps (o :: os) : List _))
                  = ((gradeDownsweeps (o :: os) : List _)) :=
              gradeDownsweeps_normal_list (o :: os)
            simp [leftPacked, rightNorm]
      _ = ((wgScanGrade (o :: os)) : List _) := by
            simp [joinList]

end WG

/-! ## Concrete IR + grades that mirror `gradeOf` -------------------------------- -/
namespace WG.IR

open Kernel
open Kernel.Examples
open Effects
open Grade
open Kernel.HasGrade
open Kernel.Lemmas

/-- Build a workgroup `Loc` for `buf[tid + shift]`. -/
@[inline] def wgLoc (shift : Int) : Kernel.Loc :=
  { space := .workgroup
  , base  := "buf"
  , idx   := { a_tid := 1, a_off := 0, b := shift } }

/-- One upsweep stage as concrete IR: guarded load, then guarded store, then barrier. -/
def upsweepBody (off : Nat) : Stmt :=
  let g  := upsweepGuard off
  let rL := wgLoc (Int.ofNat off - 1)
  let wR := wgLoc (2 * Int.ofNat off - 1)
  .ite g (.seq (.load rL "_tmp") (.store wR (.var "_tmp")))

def upsweepStmt (off : Nat) : Stmt :=
  .seq (upsweepBody off) .barrier_wg

/-- One downsweep stage as concrete IR: two guarded stores, then barrier. -/
def downsweepBody (off : Nat) : Stmt :=
  let g  := upsweepGuard off
  let wL := wgLoc (Int.ofNat off - 1)
  let wR := wgLoc (2 * Int.ofNat off - 1)
  .ite g (.seq (.store wL (.var "_a")) (.store wR (.var "_b")))

def downsweepStmt (off : Nat) : Stmt :=
  .seq (downsweepBody off) .barrier_wg

/-- All upsweep stages in list order. -/
def wgUpsweepStmt (offs : List Nat) : Stmt :=
  .for_offsets (offs.map (fun o => (o, upsweepStmt o)))

/-- All downsweep stages in reverse order (right-to-left). -/
def wgDownsweepStmt (offs : List Nat) : Stmt :=
  .for_offsets ((offs.reverse).map (fun o => (o, downsweepStmt o)))

/-- Full workgroup scan statement. -/
def wgScanStmt (offs : List Nat) : Stmt :=
  .seq (wgUpsweepStmt offs) (wgDownsweepStmt offs)

/-- IR grade for a single upsweep stage: guard-stamped read, then write, then barrier. -/
def gradeUpsweepIR (off : Nat) : Grade :=
  let g  := upsweepGuard off
  let r  := asRead (wgLoc (Int.ofNat off - 1)) guardAll
  let w  := asWrite (wgLoc (2 * Int.ofNat off - 1)) guardAll
  Grade.seq (stampGrade (Grade.seq (Grade.ofRead r) (Grade.ofWrite w)) g) Grade.ofBarrier

/-- IR grade for a single downsweep stage: two guarded writes, then barrier. -/
def gradeDownsweepIR (off : Nat) : Grade :=
  let g  := upsweepGuard off
  let wL := asWrite (wgLoc (Int.ofNat off - 1)) guardAll
  let wR := asWrite (wgLoc (2 * Int.ofNat off - 1)) guardAll
  Grade.seq (stampGrade (Grade.seq (Grade.ofWrite wL) (Grade.ofWrite wR)) g) Grade.ofBarrier

lemma gradeUpsweepIR_normalizes (off : Nat) :
    Grade.normalize (gradeUpsweepIR off) = gradeUpsweep off := by
  let p :=
    stampPhase ⟨[asRead (wgLoc (Int.ofNat off - 1)) guardAll], []⟩ (upsweepGuard off)
  let q :=
    stampPhase ⟨[], [asWrite (wgLoc (2 * Int.ofNat off - 1)) guardAll]⟩ (upsweepGuard off)
  have hp : Effects.Phase.empty p = false := by
    simp [p]
  have hq : Effects.Phase.empty q = false := by
    simp [q]
  have hfuse : Phase.fuse p q = upsweepPhase off := by
    simp [p, q, Phase.fuse, stampPhase, upsweepPhase, wgLoc, wgBuf, asRead, asWrite,
          List.append_nil, List.nil_append]
  have hshape :
      ((gradeUpsweepIR off) : List Phase)
        = [p, q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
    simp [gradeUpsweepIR, p, q, Grade.seq, stampGrade,
          Grade.ofRead, Grade.ofWrite, Grade.ofBarrier]
  have hnormList :
      ((Grade.normalize (gradeUpsweepIR off)) : List Phase)
        = normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
    calc
      ((Grade.normalize (gradeUpsweepIR off)) : List Phase)
          = normalizeList ((gradeUpsweepIR off).toList) :=
            Grade.toList_normalize (gradeUpsweepIR off)
      _ = normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
            simp [hshape]
  have hnorm :
      ((Grade.normalize (gradeUpsweepIR off)) : List Phase)
        = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] :=
    hnormList.trans
      (Effects.Grade.normalizeList_stage_pair (p := p) (q := q) hp hq)
  have hrhs :
      ((gradeUpsweep off) : List Phase)
        = [upsweepPhase off] ++ [⟨[], []⟩, ⟨[], []⟩] := by
    simp [gradeUpsweep, Grade.ofBarrier]
  refine Word.ext ?_
  calc
    ((Grade.normalize (gradeUpsweepIR off)) : List Phase)
        = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] := hnorm
    _ = [upsweepPhase off] ++ [⟨[], []⟩, ⟨[], []⟩] := by simp [hfuse]
    _ = ((gradeUpsweep off) : List Phase) := hrhs.symm

lemma gradeDownsweepIR_normalizes (off : Nat) :
    Grade.normalize (gradeDownsweepIR off) = gradeDownsweep off := by
  let p :=
    stampPhase ⟨[], [asWrite (wgLoc (Int.ofNat off - 1)) guardAll]⟩ (upsweepGuard off)
  let q :=
    stampPhase ⟨[], [asWrite (wgLoc (2 * Int.ofNat off - 1)) guardAll]⟩ (upsweepGuard off)
  have hp : Effects.Phase.empty p = false := by
    simp [p]
  have hq : Effects.Phase.empty q = false := by
    simp [q]
  have hfuse : Phase.fuse p q = downsweepPhase off := by
    simp [p, q, Phase.fuse, stampPhase, downsweepPhase, wgLoc, wgBuf, asWrite,
          List.append_nil, List.nil_append]
  have hshape :
      ((gradeDownsweepIR off) : List Phase)
        = [p, q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
    simp [gradeDownsweepIR, p, q, Grade.seq, stampGrade,
          Grade.ofWrite, Grade.ofBarrier]
  have hnormList :
      ((Grade.normalize (gradeDownsweepIR off)) : List Phase)
        = normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
    calc
      ((Grade.normalize (gradeDownsweepIR off)) : List Phase)
          = normalizeList ((gradeDownsweepIR off).toList) :=
            Grade.toList_normalize (gradeDownsweepIR off)
      _ = normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
            simp [hshape]
  have hnorm :
      ((Grade.normalize (gradeDownsweepIR off)) : List Phase)
        = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] :=
    hnormList.trans
      (Effects.Grade.normalizeList_stage_pair (p := p) (q := q) hp hq)
  have hrhs :
      ((gradeDownsweep off) : List Phase)
        = [downsweepPhase off] ++ [⟨[], []⟩, ⟨[], []⟩] := by
    simp [gradeDownsweep, Grade.ofBarrier]
  refine Word.ext ?_
  calc
    ((Grade.normalize (gradeDownsweepIR off)) : List Phase)
        = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] := hnorm
    _ = [downsweepPhase off] ++ [⟨[], []⟩, ⟨[], []⟩] := by simp [hfuse]
    _ = ((gradeDownsweep off) : List Phase) := hrhs.symm


/-- Folded IR grades matching the concrete statements. -/
def gradeUpsweepsIR : List Nat → Grade
| []      => Grade.eps
| o :: os => Grade.seq (gradeUpsweepIR o) (gradeUpsweepsIR os)

def gradeDownsweepsIR : List Nat → Grade
| []      => Grade.eps
| o :: os => Grade.seq (gradeDownsweepsIR os) (gradeDownsweepIR o)

def wgScanGradeIR (offs : List Nat) : Grade :=
  Grade.seq (gradeUpsweepsIR offs) (gradeDownsweepsIR offs)

lemma gradeUpsweepsIR_normalizes (offs : List Nat) :
    Grade.normalize (gradeUpsweepsIR offs) = WG.gradeUpsweeps offs := by
  induction offs with
  | nil =>
      simp [gradeUpsweepsIR, WG.gradeUpsweeps, Grade.eps]
  | cons o os ih =>
      let p :=
        stampPhase ⟨[asRead (wgLoc (Int.ofNat o - 1)) guardAll], []⟩ (upsweepGuard o)
      let q :=
        stampPhase ⟨[], [asWrite (wgLoc (2 * Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
      have hp : Effects.Phase.empty p = false := by
        simp [p]
      have hq : Effects.Phase.empty q = false := by
        simp [q]
      have hfuse : Phase.fuse p q = upsweepPhase o := by
        simp [p, q, Phase.fuse, stampPhase, upsweepPhase, wgLoc, wgBuf, asRead, asWrite,
              List.append_nil, List.nil_append]
      have hstage :
          ((gradeUpsweepIR o) : List Phase)
            = [p, q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
        simp [gradeUpsweepIR, p, q, Grade.seq, stampGrade,
              Grade.ofRead, Grade.ofWrite, Grade.ofBarrier]
      have hseq :
          ((gradeUpsweepsIR (o :: os)) : List Phase)
            = (gradeUpsweepIR o : List Phase)
                ++ (gradeUpsweepsIR os : List Phase) := by
        simp [gradeUpsweepsIR, Grade.seq]
      have hshape :
          ((gradeUpsweepsIR (o :: os)) : List Phase)
            = [p, q] ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ (gradeUpsweepsIR os : List Phase) := by
        calc
          ((gradeUpsweepsIR (o :: os)) : List Phase)
              = (gradeUpsweepIR o : List Phase)
                  ++ (gradeUpsweepsIR os : List Phase) := hseq
          _ = ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩])
                  ++ (gradeUpsweepsIR os : List Phase) := by
                simp [hstage]
          _ = [p, q] ++ [⟨[], []⟩, ⟨[], []⟩]
                  ++ (gradeUpsweepsIR os : List Phase) :=
            List.append_assoc [p, q] [⟨[], []⟩, ⟨[], []⟩]
              (gradeUpsweepsIR os : List Phase)
      have hnormList :
          normalizeList ((gradeUpsweepsIR (o :: os)).toList)
            = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ normalizeList ((gradeUpsweepsIR os).toList) := by
        calc
          normalizeList ((gradeUpsweepsIR (o :: os)).toList)
              = normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩]
                  ++ (gradeUpsweepsIR os : List Phase)) := by
                    simp [hshape]
          _ = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
                  ++ normalizeList ((gradeUpsweepsIR os).toList) :=
                Effects.Grade.normalizeList_stage_append
                  (p := p) (q := q) (rest := (gradeUpsweepsIR os).toList) hp hq
      have hrest :
          normalizeList ((gradeUpsweepsIR os).toList)
            = ((WG.gradeUpsweeps os) : List Phase) := by
        have hnormEq := Grade.toList_normalize (gradeUpsweepsIR os)
        have hi := congrArg Word.toList ih
        exact hnormEq.symm.trans hi
      have hnorm :
          ((Grade.normalize (gradeUpsweepsIR (o :: os))) : List Phase)
            = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ ((WG.gradeUpsweeps os) : List Phase) := by
        calc
          ((Grade.normalize (gradeUpsweepsIR (o :: os))) : List Phase)
              = normalizeList ((gradeUpsweepsIR (o :: os)).toList) :=
                Grade.toList_normalize (gradeUpsweepsIR (o :: os))
          _ = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
                  ++ normalizeList ((gradeUpsweepsIR os).toList) := hnormList
          _ = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
                  ++ ((WG.gradeUpsweeps os) : List Phase) := by
                simp [hrest]
      have hrhs :
          ((WG.gradeUpsweeps (o :: os)) : List Phase)
            = [upsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ ((WG.gradeUpsweeps os) : List Phase) := by
        calc
          ((WG.gradeUpsweeps (o :: os)) : List Phase)
              = (gradeUpsweep o : List Phase)
                  ++ (WG.gradeUpsweeps os : List Phase) := by
                simp [WG.gradeUpsweeps, Grade.seq]
          _ = ([upsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩])
                  ++ ((WG.gradeUpsweeps os) : List Phase) := by
                simp [gradeUpsweep, Grade.ofBarrier]
          _ = [upsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩]
                  ++ ((WG.gradeUpsweeps os) : List Phase) :=
            List.append_assoc [upsweepPhase o]
              [⟨[], []⟩, ⟨[], []⟩]
              ((WG.gradeUpsweeps os) : List Phase)
      have hw :
          [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
              ++ ((WG.gradeUpsweeps os) : List Phase)
            = [upsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩]
              ++ ((WG.gradeUpsweeps os) : List Phase) := by
        simp [hfuse]
      refine Word.ext ?_
      calc
        ((Grade.normalize (gradeUpsweepsIR (o :: os))) : List Phase)
            = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ ((WG.gradeUpsweeps os) : List Phase) := hnorm
        _ = [upsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ ((WG.gradeUpsweeps os) : List Phase) := hw
        _ = ((WG.gradeUpsweeps (o :: os)) : List Phase) := hrhs.symm

lemma gradeUpsweepsIR_endsWith_barrier :
  ∀ offs : List Nat, offs ≠ [] →
    ∃ xs0 : List Effects.Phase,
      (gradeUpsweepsIR offs : List Effects.Phase) = xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
| [], hne       => False.elim (hne rfl)    -- << fixed
| [o], _        =>
  by
    -- one stage: expose the two stamped phases
    let p :=
      stampPhase ⟨[asRead (wgLoc (Int.ofNat o - 1)) guardAll], []⟩ (upsweepGuard o)
    let q :=
      stampPhase ⟨[], [asWrite (wgLoc (2 * Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
    refine ⟨[p, q], ?_⟩
    simp [gradeUpsweepsIR, Grade.seq, gradeUpsweepIR, p, q,
          stampGrade, Grade.ofRead, Grade.ofWrite, Grade.ofBarrier, Grade.eps]
| o :: o' :: os, _ =>
  by
    -- split the chain at the head stage
    have hsplit :
      (gradeUpsweepsIR (o :: o' :: os)).toList
        = (gradeUpsweepIR o).toList ++ (gradeUpsweepsIR (o' :: os)).toList := by
      simp [gradeUpsweepsIR, Grade.seq]

    -- tail ends-with-barrier witness
    rcases gradeUpsweepsIR_endsWith_barrier (o' :: os) (by simp) with ⟨xs0, hx⟩

    -- choose a witness that carries the head chunk
    refine ⟨(gradeUpsweepIR o).toList ++ xs0, ?_⟩

    -- plug both equalities; associativity finishes it
    simp [hsplit, hx, List.append_assoc]

/-- Downsweep IR chain ends with the explicit barrier whenever it is nonempty. -/
lemma gradeDownsweepsIR_endsWith_barrier :
  ∀ offs : List Nat, offs ≠ [] →
    ∃ xs0 : List Effects.Phase,
      (gradeDownsweepsIR offs : List Effects.Phase) = xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
| [], hne       => False.elim (hne rfl)    -- << fixed
| [o], _        =>
  by
    -- one stage: expose the two stamped writes
    let p :=
      stampPhase ⟨[], [asWrite (wgLoc (Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
    let q :=
      stampPhase ⟨[], [asWrite (wgLoc (2 * Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
    refine ⟨[p, q], ?_⟩
    simp [gradeDownsweepsIR, Grade.seq, gradeDownsweepIR, p, q,
          stampGrade, Grade.ofWrite, Grade.ofBarrier, Grade.eps]
| o :: o' :: os, _ =>
  by
    -- chain = (left) ++ (single stage on o)
    let p :=
      stampPhase ⟨[], [asWrite (wgLoc (Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
    let q :=
      stampPhase ⟨[], [asWrite (wgLoc (2 * Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
    have hstage :
        ((gradeDownsweepIR o) : List Effects.Phase)
          = [p, q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
      simp [gradeDownsweepIR, p, q, Grade.seq, stampGrade, Grade.ofWrite, Grade.ofBarrier]
    refine ⟨(gradeDownsweepsIR (o' :: os) : List _) ++ [p, q], ?_⟩
    simp [gradeDownsweepsIR, Grade.seq, hstage, List.append_assoc]

/-- (1) The downsweep IR chain collapses under `Grade.normalize`
    to the abstract downsweep grade. -/
lemma gradeDownsweepsIR_normalizes (offs : List Nat) :
  Grade.normalize (gradeDownsweepsIR offs) = WG.gradeDownsweeps offs := by
  induction offs with
  | nil =>
      simp [gradeDownsweepsIR, WG.gradeDownsweeps, Grade.eps]
  | cons o os ih =>
      -- Work on lists via `toList_normalize`.
      have L :
          ((Grade.normalize (gradeDownsweepsIR (o :: os))) : List Effects.Phase)
            = Grade.normalizeList
                ((gradeDownsweepsIR os : List _) ++ (gradeDownsweepIR o : List _)) := by
        simp [Effects.Grade.toList_normalize, gradeDownsweepsIR, Grade.seq]
      -- expose the single-stage on the right
      let p :=
        stampPhase ⟨[], [asWrite (wgLoc (Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
      let q :=
        stampPhase ⟨[], [asWrite (wgLoc (2 * Int.ofNat o - 1)) guardAll]⟩ (upsweepGuard o)
      have hstage :
          ((gradeDownsweepIR o) : List Effects.Phase)
            = [p, q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
        simp [gradeDownsweepIR, p, q, Grade.seq, stampGrade, Grade.ofWrite, Grade.ofBarrier]
      -- split on `os`
      cases os with
      | nil =>
          -- direct single-stage collapse
          have hp : p.empty = false := by
            simp [p, Effects.Phase.empty, stampPhase]
          have hq : q.empty = false := by
            simp [q, Effects.Phase.empty, stampPhase]
          have collapse :
            Grade.normalizeList ((gradeDownsweepsIR [] : List _) ++ (gradeDownsweepIR o : List _))
              = [Effects.Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
            simpa [gradeDownsweepsIR, Grade.eps, List.nil_append, hstage]
              using Effects.Grade.normalizeList_stage_pair (p := p) (q := q) hp hq

            -- RHS normalized word for the singleton abstract chain
          have R :
            ((Grade.normalize (WG.gradeDownsweeps [o])) : List _)
              = [downsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩] := by
            -- `downsweepPhase o` is non-empty (has two writes)
            have hp2 : (downsweepPhase o).empty = false := by
              simp [downsweepPhase, Effects.Phase.empty, wgBuf]

            -- compute as lists, then normalize the singleton+barrier explicitly
            calc
              ((Grade.normalize (WG.gradeDownsweeps [o])) : List _)
                  = Effects.Grade.normalizeList ((WG.gradeDownsweeps [o]).toList) := by
                      exact Effects.Grade.toList_normalize (WG.gradeDownsweeps [o])
              _ = Effects.Grade.normalizeList
                    ((Grade.eps : Effects.Grade).toList ++ (gradeDownsweep o : List _)) := by
                      simp [WG.gradeDownsweeps, Grade.seq]
              _ = Effects.Grade.normalizeList
                    ([downsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
                      simp [Grade.eps, gradeDownsweep, Grade.ofBarrier, List.nil_append]
              _ = [downsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩] :=
                Effects.Grade.normalizeList_single_nonempty_barrier _ hp2
          have fuse_eq : Effects.Phase.fuse p q = downsweepPhase o := by
            simp [downsweepPhase, p, q, Effects.Phase.fuse, stampPhase,
                  wgLoc, wgBuf, asWrite, upsweepGuard]

                    -- We need: normalizeList (gradeDownsweepsIR [o]).toList
          --           = (WG.gradeDownsweeps [o]).toList

          -- 1) Use L and collapse to get the normalized LHS as a list
          --    ((normalize (gradeDownsweepsIR [o])) : List) = [p⋈q] ++ B
          have Lnorm :
            ((Grade.normalize (gradeDownsweepsIR [o])) : List _)
              = [Effects.Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] :=
            L.trans collapse

          -- 2) Convert to the exact goal’s LHS shape (normalizeList … .toList)
          have Llhs :
            Grade.normalizeList (gradeDownsweepsIR [o]).toList
              = [Effects.Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
            simpa [Effects.Grade.toList_normalize] using Lnorm

          -- 3) Identify the fused phase with the spec phase
          have Llhs' :
            Grade.normalizeList (gradeDownsweepsIR [o]).toList
              = [downsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩] := by
            simpa [fuse_eq]

          -- 4) Compute the raw abstract RHS list once
          have Rshape :
            ((WG.gradeDownsweeps [o]) : List _)
              = [downsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩] := by
            simp [ WG.gradeDownsweeps
                 , Grade.seq
                 , gradeDownsweep
                 , Grade.ofBarrier
                 , Grade.eps
                 , List.nil_append ]

          apply LanguageQuantale.Word.ext
          simpa [Effects.Grade.toList_normalize] using (Llhs'.trans Rshape.symm)
      | cons o' os' =>
          -- prefix ends with a barrier: cut in the middle, then fold IH and single-stage collapse
          rcases gradeDownsweepsIR_endsWith_barrier (o' :: os') (by simp) with ⟨xs0, hx⟩
          -- cut at the middle barrier, then collapse the right stage
          have cut :
            Effects.Grade.normalizeList
              ((gradeDownsweepsIR (o' :: os') : List _)
                ++ (gradeDownsweepIR o : List _))
            = Effects.Grade.normalizeList xs0
                ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ Effects.Grade.normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
            simpa [hx, hstage, List.append_assoc]
              using Effects.Grade.normalizeList_barrier_middle_append xs0
                    ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩])

          have hp : p.empty = false := by
            simp [p, stampPhase, Effects.Phase.empty]
          have hq : q.empty = false := by
            simp [q, stampPhase, Effects.Phase.empty]

          have rightChunk :
            Effects.Grade.normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩])
              = [Effects.Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] :=
            Effects.Grade.normalizeList_stage_pair (p := p) (q := q) hp hq

          -- IH converted to a list equality
          have IHlist :
            Effects.Grade.normalizeList ((gradeDownsweepsIR (o' :: os')).toList)
              = ((WG.gradeDownsweeps (o' :: os')) : List _) := by
            have := congrArg LanguageQuantale.Word.toList (by simpa using ih)
            simpa using this

          -- pack the left chunk using the right-append barrier lemma + IH
          have pack :
            Effects.Grade.normalizeList xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
              = Effects.Grade.normalizeList (xs0 ++ [⟨[], []⟩, ⟨[], []⟩]) :=
            (Effects.Grade.normalizeList_append_barrier_right xs0).symm

          have hx_norm :
            Effects.Grade.normalizeList (xs0 ++ [⟨[], []⟩, ⟨[], []⟩])
              = Effects.Grade.normalizeList ((gradeDownsweepsIR (o' :: os')).toList) :=
            (congrArg Effects.Grade.normalizeList hx).symm

          have leftPacked :
            Effects.Grade.normalizeList xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
              = ((WG.gradeDownsweeps (o' :: os')) : List _) :=
            pack.trans (hx_norm.trans IHlist)

          -- Combine with the L you already have:
          --   L : ((normalize … (o :: o' :: os')) : List _) =
          --       normalizeList ( (gradeDownsweepsIR (o' :: os')).toList
          --                       ++ (gradeDownsweepIR o).toList )
          -- collapse the right stage in `cut`
          have cut2 :
            ((Effects.Grade.normalize (gradeDownsweepsIR (o :: o' :: os'))) : List _)
              = (Effects.Grade.normalizeList xs0 ++ [⟨[], []⟩, ⟨[], []⟩])
                  ++ ([Effects.Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
            -- bring `cut` to the shape of the left-hand side via `L`
            have tmp :
              Effects.Grade.normalizeList
                (((gradeDownsweepsIR (o' :: os')) : List _)
                  ++ (gradeDownsweepIR o : List _))
                = Effects.Grade.normalizeList xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
                    ++ ([Effects.Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]) := by
              simpa [rightChunk, List.append_assoc] using cut
            simpa [L] using tmp

          -- identify the fused phase with the spec phase
          have fuse_eq : Effects.Phase.fuse p q = downsweepPhase o := by
            simp [downsweepPhase, p, q, Effects.Phase.fuse, stampPhase,
                  wgLoc, wgBuf, asWrite, upsweepGuard]

          -- Final left-hand normalized list:
          have LHS :
            ((Effects.Grade.normalize (gradeDownsweepsIR (o :: o' :: os'))) : List _)
              = ((WG.gradeDownsweeps (o' :: os')) : List _)
                  ++ [downsweepPhase o] ++ [⟨[], []⟩, ⟨[], []⟩] := by
            simpa [leftPacked, fuse_eq, List.append_assoc] using cut2

          have Rshape :
            ((WG.gradeDownsweeps (o :: o' :: os')) : List _)
              = ((WG.gradeDownsweeps (o' :: os')) : List _)
                  ++ [downsweepPhase o] ++ [⟨[],[]⟩,⟨[],[]⟩] := by
            simp [ WG.gradeDownsweeps
                , Grade.seq
                , gradeDownsweep
                , Grade.ofBarrier
                , List.append_assoc ]

          -- done
          apply LanguageQuantale.Word.ext
          exact LHS.trans Rshape.symm

/-- Helper: sequencing `gradeOfOffsets` over appended lists. -/
lemma gradeOfOffsets_append {xs ys : List (Nat × Stmt)} :
  gradeOfOffsets (xs ++ ys) = Grade.seq (gradeOfOffsets xs) (gradeOfOffsets ys) := by
  induction xs with
  | nil => simp [gradeOfOffsets, Grade.seq, Grade.eps]
  | cons x xs ih =>
      rcases x with ⟨k, s⟩
      simp [List.cons_append, gradeOfOffsets, Grade.seq, ih, mul_assoc]

/-- `gradeOf` lines up with the IR upsweep statement. -/
lemma gradeOf_upsweepStmt (off : Nat) :
  gradeOf (upsweepStmt off) = gradeUpsweepIR off := by
  simp [upsweepStmt, upsweepBody, gradeUpsweepIR, Grade.seq, gradeOf, stampGrade, wgLoc]

lemma gradeOf_downsweepStmt (off : Nat) :
  gradeOf (downsweepStmt off) = gradeDownsweepIR off := by
  simp [downsweepStmt, downsweepBody, gradeDownsweepIR, Grade.seq, gradeOf, stampGrade, wgLoc]

lemma gradeOfOffsets_upsweep (offs : List Nat) :
  gradeOfOffsets (offs.map (fun o => (o, upsweepStmt o))) = gradeUpsweepsIR offs := by
  induction offs with
  | nil => simp [gradeOfOffsets, gradeUpsweepsIR]
  | cons o os ih =>
      simp [gradeOfOffsets, gradeUpsweepsIR, gradeOf_upsweepStmt, ih, Grade.seq]

lemma gradeOfOffsets_downsweep (offs : List Nat) :
  gradeOfOffsets ((offs.reverse).map (fun o => (o, downsweepStmt o))) =
    gradeDownsweepsIR offs := by
  induction offs with
  | nil => simp [gradeOfOffsets, gradeDownsweepsIR]
  | cons o os ih =>
      have ih' :
          gradeOfOffsets
              ((List.map (fun o => (o, downsweepStmt o)) os).reverse) =
                gradeDownsweepsIR os := by
        simpa [List.map_reverse] using ih
      simp [gradeDownsweepsIR, List.reverse_cons, List.map_append, List.map,
            List.map_reverse, gradeOfOffsets_append, gradeOf_downsweepStmt, ih',
            Grade.seq, Grade.eps, gradeOfOffsets]

lemma gradeOf_wgUpsweepStmt (offs : List Nat) :
  gradeOf (wgUpsweepStmt offs) = gradeUpsweepsIR offs := by
  simpa [wgUpsweepStmt, gradeOf] using gradeOfOffsets_upsweep offs

lemma gradeOf_wgDownsweepStmt (offs : List Nat) :
  gradeOf (wgDownsweepStmt offs) = gradeDownsweepsIR offs := by
  simpa [wgDownsweepStmt, gradeOf] using gradeOfOffsets_downsweep offs

lemma gradeOf_wgScanStmt (offs : List Nat) :
  gradeOf (wgScanStmt offs) = wgScanGradeIR offs := by
  simp [wgScanStmt, wgScanGradeIR, gradeOf, gradeOf_wgUpsweepStmt, gradeOf_wgDownsweepStmt,
        Grade.seq]

/-- Read-only single phase is trivially safe. -/
private lemma read_only_safe (a : Access) :
  PhasesSafe (Word.ofList [⟨[a], []⟩]) :=
  PhasesSafe.singleton <| by
    constructor
    · intro i j off a' b' hij ha hb _ _ _
      simp at hb
    · intro i j off r w hr hw _ _
      simp at hw

/-- Write-only single phase for upsweep’s right target is safe across threads. -/
private lemma write_only_upsweep_safe (off : Nat) :
  PhasesSafe (Word.ofList
    [⟨[], [wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off)]⟩]) :=
  PhasesSafe.singleton <| by
    constructor
    · intro i j offV a b hij ha hb _ hi hj
      have ha' :
          a = wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off) := by
        simpa using ha
      have hb' :
          b = wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off) := by
        simpa using hb
      subst ha'
      subst hb'
      simpa [wgBuf, Aff2.eval] using upsweep_index_distinct off hij
    · intro i j offV r w hr _ _ _
      simp at hr

/-- Left-hand downsweep write is safe. -/
private lemma write_only_down_left_safe (off : Nat) :
  PhasesSafe (Word.ofList
    [⟨[], [wgBuf "buf" (Int.ofNat off - 1) (upsweepGuard off)]⟩]) :=
  PhasesSafe.singleton <| by
    constructor
    · intro i j offV a b hij ha hb _ hi hj
      have ha' :
          a = wgBuf "buf" (Int.ofNat off - 1) (upsweepGuard off) := by simpa using ha
      have hb' :
          b = wgBuf "buf" (Int.ofNat off - 1) (upsweepGuard off) := by simpa using hb
      subst ha'
      subst hb'
      simpa [wgBuf, Aff2.eval] using (downsweep_index_distinct_both off hij).left
    · intro i j offV r w hr _ _ _
      simp at hr

/-- Right-hand downsweep write is safe. -/
private lemma write_only_down_right_safe (off : Nat) :
  PhasesSafe (Word.ofList
    [⟨[], [wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off)]⟩]) :=
  PhasesSafe.singleton <| by
    constructor
    · intro i j offV a b hij ha hb _ hi hj
      have ha' :
          a = wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off) := by simpa using ha
      have hb' :
          b = wgBuf "buf" (2 * Int.ofNat off - 1) (upsweepGuard off) := by simpa using hb
      subst ha'
      subst hb'
      simpa [wgBuf, Aff2.eval] using (downsweep_index_distinct_both off hij).right
    · intro i j offV r w hr _ _ _
      simp at hr

/-- Each upsweep IR stage is safe: read, then write, then barrier. -/
lemma gradeUpsweepIR_safe (off : Nat) :
  PhasesSafe (gradeUpsweepIR off) := by
  dsimp [gradeUpsweepIR]
  have hread :
      PhasesSafe
        (stampGrade (Word.ofList [⟨[asRead (wgLoc (Int.ofNat off - 1)) guardAll], []⟩])
          (upsweepGuard off)) := by
    simpa [stampGrade, stampPhase, wgLoc, asRead, wgBuf] using
      read_only_safe (wgBuf "buf" (Int.ofNat off - 1) (upsweepGuard off))
  have hwrite :
      PhasesSafe
        (stampGrade (Word.ofList [⟨[], [asWrite (wgLoc (2 * Int.ofNat off - 1)) guardAll]⟩])
          (upsweepGuard off)) := by
    simpa [stampGrade, stampPhase, wgLoc, asWrite, wgBuf] using
      write_only_upsweep_safe off
  have hbar := PhasesSafe.barrier
  simpa [Grade.seq] using PhasesSafe.seq (PhasesSafe.seq hread hwrite) hbar

/-- Each downsweep IR stage is safe: two writes then a barrier. -/
lemma gradeDownsweepIR_safe (off : Nat) :
  PhasesSafe (gradeDownsweepIR off) := by
  dsimp [gradeDownsweepIR]
  have hl :
      PhasesSafe
        (stampGrade (Word.ofList [⟨[], [asWrite (wgLoc (Int.ofNat off - 1)) guardAll]⟩])
          (upsweepGuard off)) := by
    simpa [stampGrade, stampPhase, wgLoc, asWrite, wgBuf] using
      write_only_down_left_safe off
  have hr :
      PhasesSafe
        (stampGrade (Word.ofList [⟨[], [asWrite (wgLoc (2 * Int.ofNat off - 1)) guardAll]⟩])
          (upsweepGuard off)) := by
    simpa [stampGrade, stampPhase, wgLoc, asWrite, wgBuf] using
      write_only_down_right_safe off
  have hbar := PhasesSafe.barrier
  simpa [Grade.seq] using PhasesSafe.seq (PhasesSafe.seq hl hr) hbar

lemma gradeUpsweepsIR_safe {offs : List Nat} :
  PhasesSafe (gradeUpsweepsIR offs) := by
  induction offs with
  | nil => simpa [gradeUpsweepsIR] using PhasesSafe.eps
  | cons o os ih =>
      simpa [gradeUpsweepsIR, Grade.seq] using
        PhasesSafe.seq (gradeUpsweepIR_safe o) ih

lemma gradeDownsweepsIR_safe {offs : List Nat} :
  PhasesSafe (gradeDownsweepsIR offs) := by
  induction offs with
  | nil => simpa [gradeDownsweepsIR] using PhasesSafe.eps
  | cons o os ih =>
      simpa [gradeDownsweepsIR, Grade.seq] using
        PhasesSafe.seq ih (gradeDownsweepIR_safe o)

lemma wgScanGradeIR_safe {offs : List Nat} :
  PhasesSafe (wgScanGradeIR offs) := by
  simpa [wgScanGradeIR, Grade.seq] using
    PhasesSafe.seq (gradeUpsweepsIR_safe (offs := offs))
                   (gradeDownsweepsIR_safe (offs := offs))

/-- (3) The full IR scan collapses under `Grade.normalize`
    to the abstract scan grade. -/
lemma wgScanGradeIR_normalizes (offs : List Nat) :
  Grade.normalize (wgScanGradeIR offs) = WG.wgScanGrade offs := by
  classical
  cases offs with
  | nil =>
      -- Prove equality of lists and fold back via Word.ext
      apply LanguageQuantale.Word.ext
      simp [ wgScanGradeIR
           , WG.wgScanGrade
           , gradeUpsweepsIR, gradeDownsweepsIR
           , WG.gradeUpsweeps, WG.gradeDownsweeps
           , Grade.seq, Grade.eps ]
  | cons o os =>
 -- Join shape of the IR scan
      have J :
        ((wgScanGradeIR (o :: os)) : List Effects.Phase)
          = (gradeUpsweepsIR (o :: os) : List Effects.Phase)
              ++ (gradeDownsweepsIR (o :: os) : List Effects.Phase) := by
        simp [wgScanGradeIR, Grade.seq]

      -- Upsweeps end-with-barrier witness: (gradeUpsweepsIR …).toList = xs0 ++ barrier
      rcases gradeUpsweepsIR_endsWith_barrier (o :: os) (by simp) with ⟨xs0, hx⟩

      -- We’ll prove list equality and fold back with Word.ext
      apply LanguageQuantale.Word.ext

      -- LHS: normalize( IR join )  → cut at the middle barrier
      have LHS :
        ((Grade.normalize (wgScanGradeIR (o :: os))) : List Effects.Phase)
          = Effects.Grade.normalizeList xs0
              ++ [⟨[], []⟩, ⟨[], []⟩]
              ++ Effects.Grade.normalizeList ((gradeDownsweepsIR (o :: os)).toList) := by
        -- toList of normalize, then apply middle-barrier cut (rewrite join via J and hx)
        simpa [Effects.Grade.toList_normalize, J, hx, List.append_assoc]
          using Effects.Grade.normalizeList_barrier_middle_append
                 xs0 ((gradeDownsweepsIR (o :: os)).toList)

      -- Each half normalizes to the abstract form (you already proved these)
      have U :
        ((Grade.normalize (gradeUpsweepsIR (o :: os))) : List Effects.Phase)
          = ((WG.gradeUpsweeps (o :: os)) : List Effects.Phase) := by
        have := congrArg LanguageQuantale.Word.toList
                    (by simpa using gradeUpsweepsIR_normalizes (o :: os))
        simpa using this

      have D :
        ((Grade.normalize (gradeDownsweepsIR (o :: os))) : List Effects.Phase)
          = ((WG.gradeDownsweeps (o :: os)) : List Effects.Phase) := by
        have := congrArg LanguageQuantale.Word.toList
                    (by simpa using gradeDownsweepsIR_normalizes (o :: os))
        simpa using this

      -- Pack the left chunk to the abstract upsweeps list:
      --   normalizeList xs0 ++ barrier
      --     = normalizeList (xs0 ++ barrier)
      --     = normalizeList ((gradeUpsweepsIR …).toList)
      --     = ((normalize (gradeUpsweepsIR …)) : List _)
      --     = (WG.gradeUpsweeps …).toList
      have pack :
        Effects.Grade.normalizeList xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
          = Effects.Grade.normalizeList (xs0 ++ [⟨[], []⟩, ⟨[], []⟩]) :=
        (Effects.Grade.normalizeList_append_barrier_right xs0).symm

      have hx_norm :
        Effects.Grade.normalizeList (xs0 ++ [⟨[], []⟩, ⟨[], []⟩])
          = Effects.Grade.normalizeList ((gradeUpsweepsIR (o :: os)).toList) :=
        (congrArg Effects.Grade.normalizeList hx).symm

      have toNormUps :
        ((Grade.normalize (gradeUpsweepsIR (o :: os))) : List Effects.Phase)
          = Effects.Grade.normalizeList ((gradeUpsweepsIR (o :: os)).toList) :=
        Effects.Grade.toList_normalize (gradeUpsweepsIR (o :: os))

      have U_cut :
        Effects.Grade.normalizeList xs0 ++ [⟨[], []⟩, ⟨[], []⟩]
          = ((WG.gradeUpsweeps (o :: os)) : List Effects.Phase) :=
        (pack.trans (hx_norm.trans toNormUps.symm)).trans (by simpa using U)

      -- Also rewrite the right chunk to the abstract downsweep list
      have toNormDown :
        ((Grade.normalize (gradeDownsweepsIR (o :: os))) : List Effects.Phase)
          = Effects.Grade.normalizeList ((gradeDownsweepsIR (o :: os)).toList) :=
        Effects.Grade.toList_normalize (gradeDownsweepsIR (o :: os))

      -- Assemble the LHS normalized list, but orient to `normalizeList (…)` form for the final join
      have L'' :
        Effects.Grade.normalizeList ((wgScanGradeIR (o :: os)).toList)
          = ((WG.gradeUpsweeps (o :: os)) : List Effects.Phase)
              ++ ((WG.gradeDownsweeps (o :: os)) : List Effects.Phase) := by
        -- turn LHS into normalizeList form
        have : ((Grade.normalize (wgScanGradeIR (o :: os))) : List _) =
                  Effects.Grade.normalizeList ((wgScanGradeIR (o :: os)).toList) :=
          Effects.Grade.toList_normalize (wgScanGradeIR (o :: os))
        -- compose the pieces
        calc
          Effects.Grade.normalizeList ((wgScanGradeIR (o :: os)).toList)
              = ((Grade.normalize (wgScanGradeIR (o :: os))) : List _) := this.symm
          _ = Effects.Grade.normalizeList xs0
                ++ [⟨[], []⟩, ⟨[], []⟩]
                ++ Effects.Grade.normalizeList ((gradeDownsweepsIR (o :: os)).toList) := LHS
          _ = ((WG.gradeUpsweeps (o :: os)) : List _)
                ++ Effects.Grade.normalizeList ((gradeDownsweepsIR (o :: os)).toList) := by
                simp [U_cut]
          _ = ((WG.gradeUpsweeps (o :: os)) : List _)
                ++ ((WG.gradeDownsweeps (o :: os)) : List _) := by
                simpa [toNormDown] using D

      -- Raw WG join (no normalize) to close by transitivity
      have Rshape :
        ((WG.wgScanGrade (o :: os)) : List Effects.Phase)
          = ((WG.gradeUpsweeps (o :: os)) : List Effects.Phase)
              ++ ((WG.gradeDownsweeps (o :: os)) : List Effects.Phase) := by
        simp [WG.wgScanGrade, Grade.seq, LanguageQuantale.Word.toList_mul]

      -- Conclude: normalizeList (IR join) = (raw WG).toList
      exact L''.trans Rshape.symm

lemma ThreadsFree_upsweepStmt (off : Nat) :
  ThreadsFree (upsweepStmt off) := by
  unfold upsweepStmt upsweepBody
  simp [ThreadsFree]

lemma ThreadsFree_downsweepStmt (off : Nat) :
  ThreadsFree (downsweepStmt off) := by
  unfold downsweepStmt downsweepBody
  simp [ThreadsFree]

lemma ThreadsFreeOffsets_map_upsweep (offs : List Nat) :
  ThreadsFreeOffsets (offs.map (fun o => (o, upsweepStmt o))) := by
  induction offs with
  | nil => simp
  | cons o os ih =>
      simp [ih, ThreadsFree_upsweepStmt]

lemma ThreadsFreeOffsets_map_downsweep (offs : List Nat) :
  ThreadsFreeOffsets (offs.map (fun o => (o, downsweepStmt o))) := by
  induction offs with
  | nil => simp
  | cons o os ih =>
      simp [ih, ThreadsFree_downsweepStmt]

lemma ThreadsFree_wgUpsweepStmt (offs : List Nat) :
  ThreadsFree (wgUpsweepStmt offs) := by
  simpa [wgUpsweepStmt] using ThreadsFreeOffsets_map_upsweep offs

lemma ThreadsFree_wgDownsweepStmt (offs : List Nat) :
  ThreadsFree (wgDownsweepStmt offs) := by
  have h := ThreadsFreeOffsets_map_downsweep (offs.reverse)
  simpa [wgDownsweepStmt] using h

lemma ThreadsFree_wgScanStmt (offs : List Nat) :
  ThreadsFree (wgScanStmt offs) := by
  simp [wgScanStmt, ThreadsFree_wgUpsweepStmt, ThreadsFree_wgDownsweepStmt]

lemma hasGrade_forThreads_wgScanStmt {Γ : Ctx} {offs : List Nat} :
  HasGrade Γ (.for_threads (wgScanStmt offs)) (gradeOf (wgScanStmt offs)) := by
  have hb : HasGrade Γ (wgScanStmt offs) (gradeOf (wgScanStmt offs)) :=
    gradeOf_sound_noThreads (Γ := Γ) (s := wgScanStmt offs)
      (ThreadsFree_wgScanStmt offs)
  have hs : PhasesSafe (gradeOf (wgScanStmt offs)) := by
    simpa [gradeOf_wgScanStmt] using wgScanGradeIR_safe (offs := offs)
  exact HasGrade.g_for_threads hb hs

notation:50 g " ≈ " h => Effects.Grade.denote g = Effects.Grade.denote h

/-- `gradeOf` for the concrete IR normalizes to the spec grade. -/
@[simp] lemma gradeOf_wgScanStmt_normalizes (offs : List Nat) :
  Effects.Grade.normalize (Kernel.gradeOf (WG.IR.wgScanStmt offs))
    = WG.wgScanGrade offs := by
  simpa [gradeOf_wgScanStmt] using
    wgScanGradeIR_normalizes offs

lemma wgScanStmt_upToNorm (offs) :
  Kernel.gradeOf (wgScanStmt offs) ≈ wgScanGrade offs := by
  simp [Effects.Grade.denote,
    gradeOf_wgScanStmt,
    wgScanGradeIR_normalizes,
    wgScanGrade_normal]

lemma hasGrade_forThreads_wgScanStmt_upToNorm {Γ} (offs) :
  HasGrade Γ (.for_threads (wgScanStmt offs))
           (gradeOf (wgScanStmt offs))
  ∧ gradeOf (wgScanStmt offs) ≈ wgScanGrade offs :=
⟨ hasGrade_forThreads_wgScanStmt (Γ := Γ) (offs := offs)
 , wgScanStmt_upToNorm offs ⟩

end WG.IR

end Examples
end Kernel
