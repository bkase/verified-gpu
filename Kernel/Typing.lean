/-
  Kernel/Typing.lean
  Graded typing judgment Γ ⊢ s ▷ g with side-conditions for DRF in for_threads.
-/
import Effects
import Kernel.Syntax
import LanguageQuantale

namespace Kernel

open Effects
open LanguageQuantale
open Grade

/-- Environments are placeholders for now; extend with variable types as needed. -/
structure Ctx : Type where
  dummy : Unit := ()

/- ------------------------------ Helpers on Grades ------------------------------ -/

namespace Grade

/-- Shorthand: the empty grade. -/
@[inline] def eps : Effects.Grade := (1 : Effects.Grade)

/-- Build a singleton write in the current phase. -/
@[inline] def ofWrite (a : Access) : Effects.Grade :=
  Word.ofList [⟨[], [a]⟩]

/-- Build a singleton read in the current phase. -/
@[inline] def ofRead (a : Access) : Effects.Grade :=
  Word.ofList [⟨[a], []⟩]

/-- Phase boundary (we use the same boundary for wg/st; you can split later). -/
@[inline] def ofBarrier : Effects.Grade :=
  -- an empty phase appended is a convenient “cut” marker
  Word.ofList [⟨[], []⟩, ⟨[], []⟩]

/-- Sequential composition (normalization is identity in current Effects). -/
@[inline] def seq (g h : Effects.Grade) : Effects.Grade := g * h

/-- Append a workgroup/storage barrier (same cut for now). -/
@[inline] def barrierWG (g : Effects.Grade) : Effects.Grade := g * ofBarrier
@[inline] def barrierST (g : Effects.Grade) : Effects.Grade := g * ofBarrier

/-- Extract the underlying phases list (needed for side-conditions). -/
@[inline] def phases (g : Effects.Grade) : List Effects.Phase := g.toList

end Grade

/- ------------------------------ Guard stamping ------------------------------ -/

/-- Apply a Guard to all accesses in a phase. -/
def stampPhase (ph : Effects.Phase) (g : Guard) : Effects.Phase :=
  { reads  := ph.reads.map (fun a => { a with guard := g })
  , writes := ph.writes.map (fun a => { a with guard := g }) }

/-- Apply a Guard to all phases in a grade. -/
def stampGrade (gr : Effects.Grade) (g : Guard) : Effects.Grade :=
  Word.ofList <| (gr.toList.map (fun ph => stampPhase ph g))

-- These facts keep normalization proofs lightweight.
@[simp] lemma Phase.empty_stamp_read (a : Effects.Access) (g : Guard) :
    Effects.Phase.empty (stampPhase ⟨[a], []⟩ g) = false := by
  simp [stampPhase, Effects.Phase.empty]

@[simp] lemma Phase.empty_stamp_write (a : Effects.Access) (g : Guard) :
    Effects.Phase.empty (stampPhase ⟨[], [a]⟩ g) = false := by
  simp [stampPhase, Effects.Phase.empty]

/- ------------------------------ IR → primitive footprints ------------------------------ -/

/-- Default guard = all threads active. -/
@[inline] def guardAll : Guard := { step := 1, phase := 0 }

/-- Access builders from an IR Loc, guarded. -/
@[inline] def asWrite (loc : Kernel.Loc) (g : Guard := guardAll) : Access :=
  { space := loc.space, base := loc.base, idx := loc.idx, guard := g }

@[inline] def asRead (loc : Kernel.Loc) (g : Guard := guardAll) : Access :=
  { space := loc.space, base := loc.base, idx := loc.idx, guard := g }

/- ------------------------------ Typing judgment ------------------------------ -/

/-- The graded typing judgment. -/
inductive HasGrade : Ctx → Kernel.Stmt → Effects.Grade → Prop

/-- [T-Skip]
    ───────────────
    Γ ⊢ skip ▷ ε
-/
| g_skip {Γ} :
    HasGrade Γ .skip Grade.eps

/-- [T-Let] (locals have no memory effects)
    ──────────────────────────────
    Γ ⊢ let x := e ▷ ε
-/
| g_let {Γ x e} :
    HasGrade Γ (.let_ x e) Grade.eps

/-- [T-Load]
    ─────────────────────────────────────────
    Γ ⊢ load loc dst ▷ Grade.ofRead (asRead loc guardAll)
-/
| g_load {Γ loc dst} :
    HasGrade Γ (.load loc dst) (Grade.ofRead (asRead loc guardAll))

/-- [T-Store]
    ──────────────────────────────────────────
    Γ ⊢ store loc rhs ▷ Grade.ofWrite (asWrite loc guardAll)
-/
| g_store {Γ loc rhs} :
    HasGrade Γ (.store loc rhs) (Grade.ofWrite (asWrite loc guardAll))

/-- [T-Atomic] (modeled as effect-neutral)
    ───────────────────────────────
    Γ ⊢ atomicAdd loc rhs dst ▷ ε
-/
| g_atomic {Γ loc rhs dst} :
    HasGrade Γ (.atomicAdd loc rhs dst) Grade.eps

/-- [T-Seq]
    Γ ⊢ s ▷ g₁    Γ ⊢ t ▷ g₂
    ──────────────────────────
    Γ ⊢ s ;; t ▷ g₁ ⋆ g₂
-/
| g_seq {Γ s t gs gt} :
    HasGrade Γ s gs →
    HasGrade Γ t gt →
    HasGrade Γ (s ;; t) (Grade.seq gs gt)

/-- [T-Barrier-WG]
    ───────────────────────────
    Γ ⊢ barrier_wg ▷ ‖wg‖
    where ‖wg‖ ≜ `Grade.ofBarrier`
-/
| g_bar_wg {Γ} :
    HasGrade Γ .barrier_wg Grade.ofBarrier

/-- [T-Barrier-ST]
    ───────────────────────────
    Γ ⊢ barrier_st ▷ ‖st‖
    where ‖st‖ ≜ `Grade.ofBarrier`
-/
| g_bar_st {Γ} :
    HasGrade Γ .barrier_st Grade.ofBarrier

/-- [T-IfGuard]
    Γ ⊢ s ▷ g
    ──────────────────────────────
    Γ ⊢ ite guard s ▷ stamp(g, guard)
-/
| g_if_guard {Γ g s gs} :
    HasGrade Γ s gs →
    HasGrade Γ (.ite g s) (stampGrade gs g)

/-- [T-ForOffsets-∅]
    ─────────────────────────────
    Γ ⊢ for_offsets [] ▷ ε
-/
| g_for_offsets_nil {Γ} :
    HasGrade Γ (.for_offsets []) Grade.eps

/-- [T-ForOffsets-Cons]
    Γ ⊢ s ▷ g₁    Γ ⊢ for_offsets ks ▷ g₂
    ─────────────────────────────────────────
    Γ ⊢ for_offsets ((k, s) :: ks) ▷ g₁ ⋆ g₂
-/
| g_for_offsets_cons {Γ k ks s gk gks} :
    HasGrade Γ s gk →
    HasGrade Γ (.for_offsets ks) gks →
    HasGrade Γ (.for_offsets ((k, s) :: ks)) (Grade.seq gk gks)

/-- [T-ForThreads] (DRF side-conditions)
    Γ ⊢ body ▷ g      phases(g) DRF-safe
    ──────────────────────────────────────
    Γ ⊢ for_threads body ▷ g
-/
| g_for_threads {Γ body g} :
    HasGrade Γ body g →
    (∀ p ∈ Grade.phases g, WritesDisjointPhase p ∧ NoRAWIntraPhase p) →
    HasGrade Γ (.for_threads body) g

/-- The empty phase is trivially safe. -/
lemma emptyPhase_safe :
    WritesDisjointPhase ({ reads := [], writes := [] } : Effects.Phase)
  ∧ NoRAWIntraPhase ({ reads := [], writes := [] } : Effects.Phase) := by
  constructor
  · intro i j off a b hij ha hb _ _ _
    simp at ha
  · intro i j off r w hr _ _ _ _
    simp at hr

/-- Predicate bundling the DRF side-condition required by `for_threads`. -/
def PhasesSafe (g : Effects.Grade) : Prop :=
  ∀ p ∈ Grade.phases g, WritesDisjointPhase p ∧ NoRAWIntraPhase p

namespace PhasesSafe

lemma seq {g h : Effects.Grade}
    (hg : PhasesSafe g) (hh : PhasesSafe h) :
    PhasesSafe (Grade.seq g h) := by
  intro p hp
  have hmem :
      p ∈ Grade.phases g ++ Grade.phases h := by
    simpa [Grade.seq, Grade.phases, Grade.toList_mul]
      using hp
  rcases List.mem_append.mp hmem with hpg | hph
  · exact hg p hpg
  · exact hh p hph

lemma eps : PhasesSafe Grade.eps := by
  intro p hp
  have : False := by simp [Grade.eps, Grade.phases] at hp
  exact this.elim

lemma singleton {p : Effects.Phase}
    (hp : WritesDisjointPhase p ∧ NoRAWIntraPhase p) :
    PhasesSafe (Word.ofList [p]) := by
  intro q hq
  simp [Grade.phases] at hq
  subst hq
  simpa using hp

lemma barrier : PhasesSafe Grade.ofBarrier := by
  intro p hp
  have hmem : p = { reads := [], writes := [] } ∨
      p = { reads := [], writes := [] } := by
    simpa [Grade.ofBarrier, Grade.phases] using hp
  cases hmem with
  | inl hp_eq =>
      subst hp_eq
      simpa using emptyPhase_safe
  | inr hp_eq =>
      subst hp_eq
      simpa using emptyPhase_safe

end PhasesSafe

/-! ### Computable grade synthesis ----------------------------------------------------- -/

mutual
  /-- Compute a conservative grade from syntax (ignoring side-conditions and disjointness). -/
  def gradeOf : Stmt → Effects.Grade
  | .skip                => Grade.eps
  | .let_ _ _            => Grade.eps
  | .load loc _          =>
      Grade.ofRead (asRead loc guardAll)
  | .store loc _         =>
      Grade.ofWrite (asWrite loc guardAll)
  | .atomicAdd _ _ _     => Grade.eps
  | .seq s t             => Grade.seq (gradeOf s) (gradeOf t)
  | .ite g s             => stampGrade (gradeOf s) g
  | .barrier_wg          => Grade.ofBarrier
  | .barrier_st          => Grade.ofBarrier
  | .for_threads b       => gradeOf b
  | .for_offsets items   => gradeOfOffsets items

  /-- Helper: sequence the grades emitted by each offset arm. -/
  def gradeOfOffsets : List (Nat × Stmt) → Effects.Grade
  | [] => Grade.eps
  | ⟨_, body⟩ :: rest => Grade.seq (gradeOf body) (gradeOfOffsets rest)
end

/-! ## Thread-free programs and split soundness ---------------------------------/

mutual
  /-- `ThreadsFree s` means `s` contains no `for_threads`. -/
  def ThreadsFree : Stmt → Prop
  | .skip               => True
  | .let_ _ _           => True
  | .load _ _           => True
  | .store _ _          => True
  | .atomicAdd _ _ _    => True
  | .seq s t            => ThreadsFree s ∧ ThreadsFree t
  | .ite _ body         => ThreadsFree body
  | .barrier_wg         => True
  | .barrier_st         => True
  | .for_threads _      => False
  | .for_offsets items  => ThreadsFreeOffsets items

  /-- Companion predicate for offset families. -/
  def ThreadsFreeOffsets : List (Nat × Stmt) → Prop
  | []                  => True
  | (_, s) :: rest      => ThreadsFree s ∧ ThreadsFreeOffsets rest
end

@[simp] lemma ThreadsFree_skip : ThreadsFree Stmt.skip := trivial
@[simp] lemma ThreadsFree_barrier_wg : ThreadsFree Stmt.barrier_wg := trivial
@[simp] lemma ThreadsFree_barrier_st : ThreadsFree Stmt.barrier_st := trivial
@[simp] lemma ThreadsFree_for_threads {body} : ThreadsFree (.for_threads body) = False := rfl
@[simp] lemma ThreadsFree_seq {s t} :
    ThreadsFree (.seq s t) = (ThreadsFree s ∧ ThreadsFree t) := rfl
@[simp] lemma ThreadsFree_ite {g body} :
    ThreadsFree (.ite g body) = ThreadsFree body := rfl
@[simp] lemma ThreadsFree_for_offsets {ks} :
    ThreadsFree (.for_offsets ks) = ThreadsFreeOffsets ks := rfl

@[simp] lemma ThreadsFreeOffsets_nil : ThreadsFreeOffsets [] := trivial
@[simp] lemma ThreadsFreeOffsets_cons {k s rest} :
    ThreadsFreeOffsets ((k, s) :: rest) = (ThreadsFree s ∧ ThreadsFreeOffsets rest) := rfl

@[simp] lemma gradeOf_load {loc dst} :
    gradeOf (.load loc dst) = Grade.ofRead (asRead loc guardAll) := rfl

@[simp] lemma gradeOf_store {loc rhs} :
    gradeOf (.store loc rhs) = Grade.ofWrite (asWrite loc guardAll) := rfl

mutual
  /-- Soundness for the thread-free fragment (no `for_threads`). -/
  theorem gradeOf_sound_noThreads {Γ : Ctx} :
      ∀ s, ThreadsFree s → HasGrade Γ s (gradeOf s)
  | .skip,               _    => by simpa [gradeOf] using HasGrade.g_skip (Γ := Γ)
  | .let_ _ _,           _    => by simpa [gradeOf] using HasGrade.g_let (Γ := Γ)
  | .load _ _,           _    => by simpa [gradeOf] using HasGrade.g_load (Γ := Γ)
  | .store _ _,          _    => by simpa [gradeOf] using HasGrade.g_store (Γ := Γ)
  | .atomicAdd _ _ _,    _    => by simpa [gradeOf] using HasGrade.g_atomic (Γ := Γ)
  | .seq s t,            hst  =>
      by
        have hpair : ThreadsFree s ∧ ThreadsFree t := by simpa [ThreadsFree] using hst
        have hs := gradeOf_sound_noThreads (Γ := Γ) s hpair.left
        have ht := gradeOf_sound_noThreads (Γ := Γ) t hpair.right
        simpa [gradeOf] using HasGrade.g_seq hs ht
  | .ite g body,         hb   =>
      by
        have hb' : ThreadsFree body := by simpa [ThreadsFree] using hb
        have hbGrade := gradeOf_sound_noThreads (Γ := Γ) body hb'
        simpa [gradeOf] using HasGrade.g_if_guard (Γ := Γ) (g := g) (s := body)
          (gs := gradeOf body) hbGrade
  | .barrier_wg,         _    => by simpa [gradeOf] using HasGrade.g_bar_wg (Γ := Γ)
  | .barrier_st,         _    => by simpa [gradeOf] using HasGrade.g_bar_st (Γ := Γ)
  | .for_threads body,   h    => False.elim (by simp at h)
  | .for_offsets ks,     hks  =>
      by
        have hks' : ThreadsFreeOffsets ks := by simpa [ThreadsFree] using hks
        have := gradeOfOffsets_sound_noThreads (Γ := Γ) ks hks'
        simpa [gradeOf] using this

  /-- Soundness helper for thread-free offset lists. -/
  theorem gradeOfOffsets_sound_noThreads {Γ : Ctx} :
      ∀ ks, ThreadsFreeOffsets ks → HasGrade Γ (.for_offsets ks) (gradeOfOffsets ks)
  | [],        _               => by simpa [gradeOfOffsets] using HasGrade.g_for_offsets_nil (Γ := Γ)
  | (k, s)::rest, hks          =>
      by
        have hpair : ThreadsFree s ∧ ThreadsFreeOffsets rest := by simpa [ThreadsFreeOffsets] using hks
        have hs := gradeOf_sound_noThreads (Γ := Γ) s hpair.left
        have ht := gradeOfOffsets_sound_noThreads (Γ := Γ) rest hpair.right
        simpa [gradeOfOffsets] using
          HasGrade.g_for_offsets_cons (Γ := Γ)
            (k := k) (s := s) (ks := rest)
            (gk := gradeOf s) (gks := gradeOfOffsets rest)
            hs ht
end

/-- Convenience wrapper for `for_threads`: provide the DRF witness explicitly. -/
lemma hasGrade_forThreads_of_safe {Γ : Ctx} {body : Stmt} {g : Effects.Grade}
  (hb : HasGrade Γ body g) (hs : PhasesSafe g) :
  HasGrade Γ (.for_threads body) g :=
  HasGrade.g_for_threads hb hs

/-- Single-use helper for the synthesized grade of `for_threads body`. -/
lemma gradeOf_sound_forThreads {Γ : Ctx} {body : Stmt}
  (hb : HasGrade Γ body (gradeOf body))
  (hs : PhasesSafe (gradeOf body)) :
  HasGrade Γ (.for_threads body) (gradeOf (.for_threads body)) := by
  simpa [gradeOf] using hasGrade_forThreads_of_safe hb hs


end Kernel
