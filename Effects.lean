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

namespace Phase

/-- Is this phase empty (no reads, no writes)? -/
@[inline] def empty (p : Phase) : Bool :=
  match p.reads, p.writes with
  | [], [] => true
  | _,  _  => false

/-- Fuse two non-empty phases by concatenating their footprints. -/
@[inline] def fuse (p q : Phase) : Phase :=
  { reads := p.reads ++ q.reads, writes := p.writes ++ q.writes }

end Phase

/-- Our language alphabet is `Phase`. -/
abbrev PhaseLang := LanguageQuantale.Lang Phase

/-- A *grade* is a normalized word of phases (a “phase trace”). -/
abbrev Grade := LanguageQuantale.Word Phase

namespace Grade
open LanguageQuantale

private def normalizeList.loop :
    Option Phase → List Phase → List Phase → List Phase
| none, [], acc => acc
| some p, [], acc => acc ++ [p]
| none, q :: qs, acc =>
    if q.empty then
      loop none qs (acc ++ [q])
    else
      loop (some q) qs acc
| some p, q :: qs, acc =>
    if q.empty then
      loop none qs (acc ++ [p, q])
    else
      loop (some (Phase.fuse p q)) qs acc

@[simp] lemma normalizeList_loop_none_nil (acc : List Phase) :
    normalizeList.loop none [] acc = acc := rfl

@[simp] lemma normalizeList_loop_some_nil (p : Phase) (acc : List Phase) :
    normalizeList.loop (some p) [] acc = acc ++ [p] := rfl

@[simp] lemma normalizeList_loop_none_cons_empty
    {q : Phase} {qs acc}
    (hq : q.empty = true) :
    normalizeList.loop none (q :: qs) acc
      = normalizeList.loop none qs (acc ++ [q]) := by
  simp [normalizeList.loop, hq]

@[simp] lemma normalizeList_loop_none_cons_nonempty
    {q : Phase} {qs acc}
    (hq : q.empty = false) :
    normalizeList.loop none (q :: qs) acc
      = normalizeList.loop (some q) qs acc := by
  simp [normalizeList.loop, hq]

@[simp] lemma normalizeList_loop_some_cons_empty
    {p q : Phase} {qs acc}
    (hq : q.empty = true) :
    normalizeList.loop (some p) (q :: qs) acc
      = normalizeList.loop none qs (acc ++ [p, q]) := by
  simp [normalizeList.loop, hq]

@[simp] lemma normalizeList_loop_some_cons_nonempty
    {p q : Phase} {qs acc}
    (hq : q.empty = false) :
    normalizeList.loop (some p) (q :: qs) acc
      = normalizeList.loop (some (Phase.fuse p q)) qs acc := by
  simp [normalizeList.loop, hq]

/-- Accumulator prefixing lemma for the normalizer loop. -/
lemma normalizeList_loop_append
    (curr : Option Phase) (ps acc : List Phase) :
    normalizeList.loop curr ps acc
      = acc ++ normalizeList.loop curr ps [] := by
  induction ps generalizing curr acc with
  | nil =>
      cases curr <;> simp
  | cons q qs ih =>
      cases curr with
      | none =>
          by_cases hq : q.empty = true
          ·
            have hleft :=
              normalizeList_loop_none_cons_empty
                (q := q) (qs := qs) (acc := acc) hq
            have hright_eq :=
              normalizeList_loop_none_cons_empty
                (q := q) (qs := qs) (acc := []) hq
            have hright := hright_eq
            simp [List.nil_append] at hright
            have hIH_acc := ih (curr := none) (acc := acc ++ [q])
            have hIH_q :=
              (ih (curr := none) (acc := [q])).symm
            have hIH_q' := congrArg (fun xs => acc ++ xs) hIH_q
            calc
              normalizeList.loop none (q :: qs) acc
                  = normalizeList.loop none qs (acc ++ [q]) := hleft
              _ = (acc ++ [q]) ++ normalizeList.loop none qs [] := hIH_acc
              _ = acc ++ ([q] ++ normalizeList.loop none qs []) := by
                    simp [List.append_assoc]
              _ = acc ++ normalizeList.loop none qs [q] := hIH_q'
              _ = acc ++ normalizeList.loop none (q :: qs) [] := by
                    simp [hright]
          ·
            have hstep :
                normalizeList.loop none (q :: qs) acc
                  = normalizeList.loop (some q) qs acc := by
              simp [normalizeList_loop_none_cons_nonempty, hq]
            have hstep₀ :
                normalizeList.loop none (q :: qs) []
                  = normalizeList.loop (some q) qs [] := by
              simp [normalizeList_loop_none_cons_nonempty, hq]
            have hIH_some := ih (curr := some q) (acc := acc)
            calc
              normalizeList.loop none (q :: qs) acc
                  = normalizeList.loop (some q) qs acc := hstep
              _ = acc ++ normalizeList.loop (some q) qs [] := hIH_some
              _ = acc ++ normalizeList.loop none (q :: qs) [] := by
                    simp [hstep₀]
      | some p =>
          by_cases hq : q.empty = true
          ·
            have hleft :=
              normalizeList_loop_some_cons_empty
                (p := p) (q := q) (qs := qs) (acc := acc) hq
            have hright_eq :=
              normalizeList_loop_some_cons_empty
                (p := p) (q := q) (qs := qs) (acc := []) hq
            have hright := hright_eq
            simp [List.nil_append] at hright
            have hIH_acc := ih (curr := none) (acc := acc ++ [p, q])
            have hIH_pq :=
              (ih (curr := none) (acc := [p, q])).symm
            have hIH_pq' := congrArg (fun xs => acc ++ xs) hIH_pq
            calc
              normalizeList.loop (some p) (q :: qs) acc
                  = normalizeList.loop none qs (acc ++ [p, q]) := hleft
              _ = (acc ++ [p, q]) ++ normalizeList.loop none qs [] := hIH_acc
              _ = acc ++ ([p, q] ++ normalizeList.loop none qs []) := by
                    simp [List.append_assoc]
              _ = acc ++ normalizeList.loop none qs [p, q] := hIH_pq'
              _ = acc ++ normalizeList.loop (some p) (q :: qs) [] := by
                    simp [hright]
          ·
            have hstep :
                normalizeList.loop (some p) (q :: qs) acc
                  = normalizeList.loop (some (Phase.fuse p q)) qs acc := by
              simp [normalizeList_loop_some_cons_nonempty, hq]
            have hstep₀ :
                normalizeList.loop (some p) (q :: qs) []
                  = normalizeList.loop (some (Phase.fuse p q)) qs [] := by
              simp [normalizeList_loop_some_cons_nonempty, hq]
            have hIH_fuse := ih (curr := some (Phase.fuse p q)) (acc := acc)
            calc
              normalizeList.loop (some p) (q :: qs) acc
                  = normalizeList.loop (some (Phase.fuse p q)) qs acc := hstep
              _ = acc ++ normalizeList.loop (some (Phase.fuse p q)) qs [] := hIH_fuse
              _ = acc ++ normalizeList.loop (some p) (q :: qs) [] := by
                    simp [hstep₀]

lemma normalizeList_loop_none_append (ps acc : List Phase) :
    normalizeList.loop none ps acc
      = acc ++ normalizeList.loop none ps [] :=
  normalizeList_loop_append none ps acc

lemma normalizeList_loop_some_append (p : Phase) (ps acc : List Phase) :
    normalizeList.loop (some p) ps acc
      = acc ++ normalizeList.loop (some p) ps [] :=
  normalizeList_loop_append (some p) ps acc

/-- Compress a list of phases by merging maximal runs of non-empty phases.
    Empty phases act as *hard* cuts and are preserved. -/
def normalizeList (xs : List Phase) : List Phase :=
  normalizeList.loop none xs []

@[simp] lemma list_singleton_append {α} (x : α) (xs : List α) :
    [x] ++ xs = x :: xs := rfl

@[simp] lemma normalizeList_cons_empty {p : Phase} {ps : List Phase}
    (hp : p.empty = true) :
    normalizeList (p :: ps) = p :: normalizeList ps := by
  unfold normalizeList
  have hstep :=
      normalizeList_loop_none_cons_empty
        (q := p) (qs := ps) (acc := []) (hq := hp)
  have hstep' := hstep
  simp [List.nil_append] at hstep'
  have happ :
      normalizeList.loop none ps [p]
        = p :: normalizeList.loop none ps [] := by
    simpa [List.nil_append, list_singleton_append] using
      (normalizeList_loop_none_append (ps := ps) (acc := [p]))
  calc
    normalizeList.loop none (p :: ps) []
        = normalizeList.loop none ps [p] := hstep'
    _ = p :: normalizeList.loop none ps [] := happ
    _ = p :: normalizeList ps := rfl

@[simp] lemma normalizeList_barrier :
    normalizeList [⟨[], []⟩, ⟨[], []⟩] = [⟨[], []⟩, ⟨[], []⟩] := by
  unfold normalizeList
  simp [Phase.empty, List.nil_append]

@[simp] lemma normalizeList_barrier_append (rest : List Phase) :
    normalizeList ([⟨[], []⟩, ⟨[], []⟩] ++ rest)
      = [⟨[], []⟩, ⟨[], []⟩] ++ normalizeList rest := by
  unfold normalizeList
  have hstep :
      normalizeList.loop none ([⟨[], []⟩, ⟨[], []⟩] ++ rest) []
        = normalizeList.loop none rest ([⟨[], []⟩, ⟨[], []⟩]) := by
    simp [List.cons_append, Phase.empty, List.nil_append]
  have happ :=
      normalizeList_loop_none_append
        (ps := rest) (acc := [⟨[], []⟩, ⟨[], []⟩])
  simpa [hstep, normalizeList]

lemma normalizeList_stage_append (p q : Phase) (rest : List Phase)
    (hp : p.empty = false) (hq : q.empty = false) :
    normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩] ++ rest)
      = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] ++ normalizeList rest := by
  unfold normalizeList
  have hstep :
      normalizeList.loop none
        ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩] ++ rest) []
        = normalizeList.loop none rest
            ([Phase.fuse p q, ⟨[], []⟩, ⟨[], []⟩]) := by
    have h1 :
        normalizeList.loop none
            (p :: q :: ⟨[], []⟩ :: ⟨[], []⟩ :: rest) []
          = normalizeList.loop (some p)
              (q :: ⟨[], []⟩ :: ⟨[], []⟩ :: rest) [] := by
      simp [normalizeList_loop_none_cons_nonempty, hp]
    have h2 :
        normalizeList.loop (some p)
            (q :: ⟨[], []⟩ :: ⟨[], []⟩ :: rest) []
          = normalizeList.loop (some (Phase.fuse p q))
              (⟨[], []⟩ :: ⟨[], []⟩ :: rest) [] := by
      simp [normalizeList_loop_some_cons_nonempty, hq]
    have h3 :
        normalizeList.loop (some (Phase.fuse p q))
            (⟨[], []⟩ :: ⟨[], []⟩ :: rest) []
          = normalizeList.loop none
              (⟨[], []⟩ :: rest)
              ([Phase.fuse p q, ⟨[], []⟩]) := by
      simp [normalizeList_loop_some_cons_empty, Phase.empty, List.nil_append]
    have h4 :
        normalizeList.loop none
            (⟨[], []⟩ :: rest)
            ([Phase.fuse p q, ⟨[], []⟩])
          = normalizeList.loop none rest
              ([Phase.fuse p q, ⟨[], []⟩, ⟨[], []⟩]) := by
      simp [normalizeList_loop_none_cons_empty, Phase.empty,
            List.nil_append]
    simpa [List.cons_append]
      using (h1.trans h2).trans (h3.trans h4)
  have happ :
      normalizeList.loop none rest
          ([Phase.fuse p q, ⟨[], []⟩, ⟨[], []⟩])
        = [Phase.fuse p q, ⟨[], []⟩, ⟨[], []⟩]
            ++ normalizeList.loop none rest [] := by
    simpa [List.nil_append] using
      normalizeList_loop_none_append
        (ps := rest)
        (acc := [Phase.fuse p q, ⟨[], []⟩, ⟨[], []⟩])
  calc
    normalizeList.loop none
        ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩] ++ rest) []
        = normalizeList.loop none rest
            ([Phase.fuse p q, ⟨[], []⟩, ⟨[], []⟩]) := hstep
    _ = [Phase.fuse p q, ⟨[], []⟩, ⟨[], []⟩]
            ++ normalizeList.loop none rest [] := happ
    _ = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩]
            ++ normalizeList rest := by
          simp [normalizeList]

lemma normalizeList_stage_pair (p q : Phase)
    (hp : p.empty = false) (hq : q.empty = false) :
    normalizeList ([p, q] ++ [⟨[], []⟩, ⟨[], []⟩])
      = [Phase.fuse p q] ++ [⟨[], []⟩, ⟨[], []⟩] := by
  simpa [normalizeList, List.cons_append]
      using normalizeList_stage_append (p := p) (q := q) (rest := []) hp hq

/-! ### Normalizer cuts at the explicit barrier -/

@[simp] lemma empty_canonical : (⟨[], []⟩ : Phase).empty = true := rfl

private lemma normalizeList_loop_append_barrier_right
    (curr : Option Phase) (xs acc : List Phase) :
    normalizeList.loop curr (xs ++ [⟨[], []⟩, ⟨[], []⟩]) acc
      = normalizeList.loop curr xs acc ++ [⟨[], []⟩, ⟨[], []⟩] := by
  revert curr acc
  induction xs with
  | nil =>
      intro curr acc
      cases curr with
      | none =>
          simp [normalizeList.loop, List.append_assoc, empty_canonical]
      | some p =>
          simp [normalizeList.loop, List.append_assoc, empty_canonical]
  | cons x xs ih =>
      intro curr acc
      cases curr with
      | none =>
          cases hxeq : x.empty with
          | false =>
              have := ih (curr := some x) (acc := acc)
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this
          | true =>
              have := ih (curr := none) (acc := acc ++ [x])
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this
      | some p =>
          cases hxeq : x.empty with
          | false =>
              have := ih (curr := some (Phase.fuse p x)) (acc := acc)
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this
          | true =>
              have := ih (curr := none) (acc := acc ++ [p, x])
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this

/-- Appending the explicit barrier pair on the right just appends it after normalization. -/
lemma normalizeList_append_barrier_right (xs : List Phase) :
    normalizeList (xs ++ [⟨[], []⟩, ⟨[], []⟩])
      = normalizeList xs ++ [⟨[], []⟩, ⟨[], []⟩] := by
  simpa [normalizeList]
    using normalizeList_loop_append_barrier_right (curr := none) (xs := xs) (acc := [])

private lemma normalizeList_loop_after_barrier
    (curr : Option Phase) (xs ys acc : List Phase) :
    normalizeList.loop curr (xs ++ [⟨[], []⟩, ⟨[], []⟩] ++ ys) acc
      = normalizeList.loop none ys
          (normalizeList.loop curr (xs ++ [⟨[], []⟩, ⟨[], []⟩]) acc) := by
  revert curr acc
  induction xs with
  | nil =>
      intro curr acc
      cases curr with
      | none =>
          simp [normalizeList.loop, List.append_assoc, empty_canonical]
      | some p =>
          simp [normalizeList.loop, List.append_assoc, empty_canonical]
  | cons x xs ih =>
      intro curr acc
      cases curr with
      | none =>
          cases hxeq : x.empty with
          | false =>
              have := ih (curr := some x) (acc := acc)
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this
          | true =>
              have := ih (curr := none) (acc := acc ++ [x])
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this
      | some p =>
          cases hxeq : x.empty with
          | false =>
              have := ih (curr := some (Phase.fuse p x)) (acc := acc)
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this
          | true =>
              have := ih (curr := none) (acc := acc ++ [p, x])
              simpa [normalizeList.loop, List.cons_append, hxeq, List.append_assoc]
                using this

/-- Middle-barrier cut: normalization splits across the explicit barrier pair. -/
lemma normalizeList_barrier_middle_append (xs ys : List Phase) :
    normalizeList (xs ++ [⟨[], []⟩, ⟨[], []⟩] ++ ys)
      = normalizeList xs ++ [⟨[], []⟩, ⟨[], []⟩] ++ normalizeList ys := by
  have hcut :=
    normalizeList_loop_after_barrier (curr := none)
        (xs := xs) (ys := ys) (acc := [])
  have happ :=
    normalizeList_loop_none_append
      (ps := ys)
      (acc := normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩]) [])
  have hprefix :=
    normalizeList_loop_append_barrier_right (curr := none)
      (xs := xs) (acc := [])
  unfold normalizeList at hcut ⊢
  have hcut' :
      normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩] ++ ys) []
        = normalizeList.loop none ys
            (normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩]) []) := hcut
  have happ' :
      normalizeList.loop none ys
          (normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩]) [])
        = normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩]) []
            ++ normalizeList.loop none ys [] := happ
  have hprefix' :
      normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩]) []
        = normalizeList.loop none xs [] ++ [⟨[], []⟩, ⟨[], []⟩] := hprefix
  calc
    normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩] ++ ys) []
        = normalizeList.loop none ys
            (normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩]) []) := hcut'
    _ = normalizeList.loop none (xs ++ [⟨[], []⟩, ⟨[], []⟩]) []
            ++ normalizeList.loop none ys [] := happ'
    _ = (normalizeList.loop none xs [] ++ [⟨[], []⟩, ⟨[], []⟩])
            ++ normalizeList.loop none ys [] := by
          simp [hprefix', List.append_assoc]

/-- A single non-empty phase is a fixed point of `normalizeList`. -/
@[simp] lemma normalizeList_single_nonempty
  (r : Phase) (hr : r.empty = false) :
  normalizeList [r] = [r] := by
  -- unfold to the loop and take 1 non-empty step, then flush the pending
  unfold normalizeList
  have hstep :
      normalizeList.loop none (r :: []) []
        = normalizeList.loop (some r) [] [] := by
    -- none + non-empty head → some r
    simp [normalizeList.loop, hr]
  calc
    normalizeList.loop none (r :: []) []
        = normalizeList.loop (some r) [] [] := hstep
    _ = [] ++ [r] := by simp      -- flush pending r
    _ = [r] := by simp

/-- A single non-empty phase followed by the explicit barrier pair is a fixed point. -/
lemma normalizeList_single_nonempty_barrier
  (r : Phase) (hr : r.empty = false) :
  normalizeList ([r] ++ [⟨[], []⟩, ⟨[], []⟩])
    = [r] ++ [⟨[], []⟩, ⟨[], []⟩] := by
  -- cut at the right barrier, then use the single-nonempty lemma
  simpa [normalizeList_single_nonempty r hr]
    using normalizeList_append_barrier_right (xs := [r])

/-- Normalize a grade: fuse adjacent non-empty phases, never across empties. -/
def normalize (g : Grade) : Grade :=
  match g with
  | ⟨phs⟩ => Word.ofList (normalizeList phs)

@[simp] lemma normalize_ofList (xs : List Phase) :
    normalize (Word.ofList xs) = Word.ofList (normalizeList xs) := rfl

@[simp] lemma toList_normalize (g : Grade) :
    (normalize g : List Phase) = normalizeList g.toList := by
  cases g; simp [normalize]

@[simp] lemma normalize_one : Grade.normalize (1 : Grade) = 1 := by
  rfl

/-- Sequential composition **without** implicit normalization. -/
@[inline] def seq_raw (g h : Grade) : Grade := (g * h)

/-- We keep the public `seq` as the raw concatenation (no hidden rewrites); the
    normalizer is explicit and used only where we prove equivalences. -/
@[inline] def seq (g h : Grade) : Grade := seq_raw g h

@[inline] def ofBarrier : Grade := Word.ofList [⟨[], []⟩, ⟨[], []⟩]

/-- Insert a *barrier* by starting a new empty phase at the end. -/
@[inline] def barrier (g : Grade) : Grade := g * ofBarrier

/-- The empty grade (no phases). -/
def unit : Grade := 1

/-- Sequential composition lemma for underlying lists. -/
@[simp] lemma toList_mul (g h : Grade) :
    ((g * h : Grade) : List Phase) = g.toList ++ h.toList :=
  Word.toList_mul g h

/-- Singleton-language denotation of a grade, quotienting by normalization. -/
def denote (g : Grade) : PhaseLang := { Grade.normalize g }

/-- Denotation of sequential composition normalizes the concatenation. -/
lemma denote_seq (g h : Grade) :
  denote (seq g h) = { Grade.normalize (g * h) } := by
  simp [denote, Grade.seq, Grade.seq_raw]

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
