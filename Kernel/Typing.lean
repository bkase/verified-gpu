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

/-- [T-Load-wg/st]
    ─────────────────────────────────────────
    Γ ⊢ load loc dst ▷ read(loc)
    where read(loc) ≜ `Grade.ofRead (asRead loc guardAll)`
-/
| g_load {Γ loc dst} :
    HasGrade Γ (.load loc dst)
      (match loc.space with
       | .workgroup => Grade.ofRead (asRead loc guardAll)
       | .storage   => Grade.ofRead (asRead loc guardAll))

/-- [T-Store-wg/st]
    ──────────────────────────────────────────
    Γ ⊢ store loc rhs ▷ write(loc)
    where write(loc) ≜ `Grade.ofWrite (asWrite loc guardAll)`
-/
| g_store {Γ loc rhs} :
    HasGrade Γ (.store loc rhs)
      (match loc.space with
       | .workgroup => Grade.ofWrite (asWrite loc guardAll)
       | .storage   => Grade.ofWrite (asWrite loc guardAll))

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

/-! ### Computable grade synthesis ----------------------------------------------------- -/

mutual
  /-- Compute a conservative grade from syntax (ignoring side-conditions and disjointness). -/
  def gradeOf : Stmt → Effects.Grade
  | .skip                => Grade.eps
  | .let_ _ _            => Grade.eps
  | .load loc _          =>
      match loc.space with
      | .workgroup => Grade.ofRead (asRead loc guardAll)
      | .storage   => Grade.ofRead (asRead loc guardAll)
  | .store loc _         =>
      match loc.space with
      | .workgroup => Grade.ofWrite (asWrite loc guardAll)
      | .storage   => Grade.ofWrite (asWrite loc guardAll)
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

mutual
  /-- Soundness sketch: the synthesized grade is derivable, assuming future lemmas discharge
      the side-conditions for barriers/loops. -/
  theorem gradeOf_sound {Γ} : ∀ s, HasGrade Γ s (gradeOf s)
  | .skip =>
      by simpa [gradeOf] using HasGrade.g_skip (Γ := Γ)
  | .let_ name expr =>
      by simpa [gradeOf] using HasGrade.g_let (Γ := Γ) (x := name) (e := expr)
  | .load loc dst =>
      by simpa [gradeOf] using HasGrade.g_load (Γ := Γ) (loc := loc) (dst := dst)
  | .store loc rhs =>
      by simpa [gradeOf] using HasGrade.g_store (Γ := Γ) (loc := loc) (rhs := rhs)
  | .atomicAdd loc rhs dst =>
      by simpa [gradeOf] using HasGrade.g_atomic (Γ := Γ) (loc := loc) (rhs := rhs) (dst := dst)
  | .seq s t =>
      by simpa [gradeOf] using HasGrade.g_seq (gradeOf_sound (Γ := Γ) s) (gradeOf_sound (Γ := Γ) t)
  | .ite guard body =>
      by
        simpa [gradeOf] using HasGrade.g_if_guard (Γ := Γ) (g := guard) (s := body)
          (gs := gradeOf body) (gradeOf_sound (Γ := Γ) body)
  | .barrier_wg =>
      by simpa [gradeOf] using HasGrade.g_bar_wg (Γ := Γ)
  | .barrier_st =>
      by simpa [gradeOf] using HasGrade.g_bar_st (Γ := Γ)
  | .for_threads body =>
      by
        -- TODO: discharge the DRF side-condition witnesses emitted by `HasGrade.g_for_threads`.
        admit
  | .for_offsets items =>
      by simpa [gradeOf] using gradeOfOffsets_sound (Γ := Γ) items

  /-- Auxiliary soundness for `gradeOfOffsets`. -/
  theorem gradeOfOffsets_sound {Γ} : ∀ items, HasGrade Γ (.for_offsets items) (gradeOfOffsets items)
  | [] =>
      by simpa [gradeOfOffsets] using HasGrade.g_for_offsets_nil (Γ := Γ)
  | ⟨k, body⟩ :: rest =>
      by
        have hb : HasGrade Γ body (gradeOf body) := gradeOf_sound (Γ := Γ) body
        have ht : HasGrade Γ (.for_offsets rest) (gradeOfOffsets rest) :=
          gradeOfOffsets_sound (Γ := Γ) rest
        simpa [gradeOfOffsets] using
          HasGrade.g_for_offsets_cons (Γ := Γ) (k := k) (s := body) (ks := rest)
            (gk := gradeOf body) (gks := gradeOfOffsets rest) hb ht
end

/-- Convenience wrapper with implicit context. -/
theorem gradeOf_sound' {Γ s} : HasGrade Γ s (gradeOf s) := gradeOf_sound (Γ := Γ) s

end Kernel
