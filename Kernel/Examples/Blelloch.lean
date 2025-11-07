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
  classical
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
  classical
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
  classical
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

/-- Final wrapper: synthesize `for_threads` over the concrete scan body. -/
lemma hasGrade_forThreads_wgScanStmt {Γ : Ctx} {offs : List Nat} :
  HasGrade Γ (.for_threads (wgScanStmt offs)) (gradeOf (wgScanStmt offs)) := by
  have hb : HasGrade Γ (wgScanStmt offs) (gradeOf (wgScanStmt offs)) :=
    gradeOf_sound_noThreads (Γ := Γ) (s := wgScanStmt offs)
      (ThreadsFree_wgScanStmt offs)
  have hs : PhasesSafe (gradeOf (wgScanStmt offs)) := by
    simpa [gradeOf_wgScanStmt] using wgScanGradeIR_safe (offs := offs)
  exact HasGrade.g_for_threads hb hs

end WG.IR

end Examples
end Kernel
