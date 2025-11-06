import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Lattice
import LanguageQuantale

namespace Effects

-- Enable pointwise set operations on languages.
open scoped Pointwise

/-- WGSL-like address spaces we care about for DRF. -/
inductive Space | workgroup | storage deriving DecidableEq, Repr

/-- A simple guard to indicate which threads are active in this access.
    For now: tid % step = phase. Extend as needed. -/
structure Guard where
  step  : Nat := 1
  phase : Nat := 0
deriving DecidableEq, Repr

/-- A tiny affine index in (tid,off): i = a_tid*tid + a_off*off + b. -/
structure Aff2 where
  a_tid : Int := 1
  a_off : Int := 0
  b     : Int := 0
deriving DecidableEq, Repr

def Aff2.eval (f : Aff2) (tid off : Int) : Int :=
  f.a_tid * tid + f.a_off * off + f.b

/-- One symbolic memory access inside a phase. -/
structure Access where
  space : Space
  base  : String
  idx   : Aff2
  guard : Guard
deriving DecidableEq, Repr

/-- One phase = the read/write footprint that must be race-free internally. -/
structure Phase where
  reads  : List Access := []
  writes : List Access := []
deriving DecidableEq, Repr

/-- Our language alphabet is `Phase`. -/
abbrev PhaseLang := LanguageQuantale.Lang Phase

/-- A *grade* is a normalized word of phases (a “phase trace”). -/
abbrev Grade := LanguageQuantale.Word Phase

namespace Grade
open LanguageQuantale

/-- View the underlying list of phases. -/
@[simp] lemma toList_mul (g h : Grade) :
    ((g * h : Grade) : List Phase) = g.toList ++ h.toList :=
  Word.toList_mul g h

/-- Normalize: fuse adjacent empty boundaries (optional: keep simple for now). -/
def normalize (g : Grade) : Grade := g   -- plug in a real normalizer later if you want

/-- Sequential composition = concatenate phase lists, then normalize. -/
def seq (g h : Grade) : Grade := normalize (g * h)

/-- Insert a *barrier* by starting a new empty phase at the end. -/
def barrier (g : Grade) : Grade :=
  normalize (Word.snoc g ⟨[], []⟩)

/-- The empty grade (no phases). -/
def unit : Grade := 1


/-- `normalize` currently does nothing. -/
@[simp] lemma normalize_eq (g : Grade) : normalize g = g := rfl

/-- Singleton-language denotation of a concrete grade. -/
def denote (g : Grade) : PhaseLang := { g }

/-- Homomorphism laws you’ll use constantly. -/
lemma denote_seq (g h : Grade) :
  denote (seq g h) = (denote g) * (denote h) := by
  ext w; constructor
  · intro hw
    have hw' : w = g * h := by
      simpa [denote, seq, normalize_eq, Set.mem_singleton_iff] using hw
    subst hw'
    refine ⟨g, ?_, h, ?_, rfl⟩
    · simp [denote]
    · simp [denote]
  · intro hw
    rcases hw with ⟨u, hu, v, hv, hcat⟩
    have hu' : u = g := by
      simpa [denote, Set.mem_singleton_iff] using hu
    have hv' : v = h := by
      simpa [denote, Set.mem_singleton_iff] using hv
    have hword : w = g * h := by
      simpa [hu', hv'] using hcat.symm
    have hw' : w ∈ ({g * h} : PhaseLang) := by
      subst hword
      simp
    simpa [denote, seq, normalize_eq] using hw'

lemma denote_unit : denote unit = (1 : PhaseLang) := by
  ext w; constructor <;> intro hw
  · have : w = (1 : Grade) := by
      simpa [denote, unit, Set.mem_singleton_iff] using hw
    exact mem_one_lang.mpr this
  · have : w = (1 : Grade) := mem_one_lang.mp hw
    simp [denote, unit, Set.mem_singleton_iff, this]

/-- Append a write access to the *current* phase. -/
def addWrite (a : Access) (g : Grade) : Grade :=
  match g with
  | ⟨phases⟩ =>
      match phases.reverse with
      | [] => Word.ofList [⟨[], [a]⟩]
      | p :: rest =>
          Word.ofList
            ((rest.reverse) ++ [⟨p.reads, p.writes ++ [a]⟩])

/-- Append a read access to the *current* phase. -/
def addRead (a : Access) (g : Grade) : Grade :=
  match g with
  | ⟨phases⟩ =>
      match phases.reverse with
      | [] => Word.ofList [⟨[a], []⟩]
      | p :: rest =>
          Word.ofList
            ((rest.reverse) ++ [⟨p.reads ++ [a], p.writes⟩])

/-- Start a new phase (i.e., place a barrier in the grade). -/
def addBarrierWG (g : Grade) : Grade := barrier g
def addBarrierST (g : Grade) : Grade := barrier g

end Grade

/-- A phase’s writes are pairwise disjoint across *distinct* thread ids,
    under a concrete offset value `off`. -/
def WritesDisjointPhase (phase : Phase) : Prop :=
  ∀ (i j : Nat) (off : Int) {a b : Access},
    i ≠ j →
    a ∈ phase.writes →
    b ∈ phase.writes →
    a.base = b.base →
    -- Guard activity for i and j:
    (i % a.guard.step = a.guard.phase % a.guard.step) →
    (j % b.guard.step = b.guard.phase % b.guard.step) →
    -- Different concrete addresses:
    a.idx.eval (Int.ofNat i) off ≠ b.idx.eval (Int.ofNat j) off

/-- Same idea for *no RAW hazard inside the same phase*. Often implied by
    disjoint writes plus “reads come from earlier phases,” but leave a hook. -/
def NoRAWIntraPhase (phase : Phase) : Prop :=
  ∀ (i j : Nat) (off : Int) {r w : Access},
    r ∈ phase.reads →
    w ∈ phase.writes →
    -- if both active, they must not alias:
    (i % r.guard.step = r.guard.phase % r.guard.step) →
    (j % w.guard.step = w.guard.phase % w.guard.step) →
    r.base ≠ w.base ∨
    r.idx.eval (Int.ofNat i) off ≠ w.idx.eval (Int.ofNat j) off


end Effects
