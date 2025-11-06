import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Lattice

open Set
open scoped Pointwise

namespace LanguageQuantale

/-- Words are just lists, wrapped to localize the concatenation instances. -/
structure Word (α : Type*) where
  toList : List α
deriving DecidableEq, Repr

namespace Word

@[ext] lemma ext {w₁ w₂ : Word α} (h : w₁.toList = w₂.toList) : w₁ = w₂ := by
  cases w₁; cases w₂; simpa using h

instance : Coe (Word α) (List α) := ⟨Word.toList⟩
instance : Coe (List α) (Word α) := ⟨fun xs => ⟨xs⟩⟩

@[simp] lemma coe_mk (xs : List α) : ((Word.mk xs : Word α) : List α) = xs := rfl
@[simp] lemma mk_coe (w : Word α) : Word.mk (w.toList) = w := by cases w; rfl
@[simp] lemma toList_coe (w : Word α) : ((w : Word α) : List α) = w.toList := rfl

/-- Build a word from a list. -/
@[simp] def ofList (xs : List α) : Word α := ⟨xs⟩

@[simp] lemma toList_ofList (xs : List α) :
    (ofList xs : Word α).toList = xs := rfl

@[simp] lemma ofList_toList (w : Word α) : ofList w.toList = w := by cases w; rfl

/-- The empty word. -/
@[simp] def nil : Word α := ofList []

instance : Mul (Word α) :=
  ⟨fun w₁ w₂ => ⟨w₁.toList ++ w₂.toList⟩⟩

@[simp] lemma toList_mul (w₁ w₂ : Word α) :
    ((w₁ * w₂ : Word α) : List α) = w₁.toList ++ w₂.toList := rfl

/-- Append a single letter to the right of a word. -/
def snoc (w : Word α) (a : α) : Word α :=
  ofList (w.toList ++ [a])

@[simp] lemma toList_snoc (w : Word α) (a : α) :
    (snoc w a).toList = w.toList ++ [a] := rfl

/-- Reverse a word. -/
def reverse (w : Word α) : Word α :=
  ofList w.toList.reverse

@[simp] lemma toList_reverse (w : Word α) :
    (reverse w).toList = w.toList.reverse := rfl

@[simp] lemma toList_nil : (nil : Word α).toList = [] := rfl

instance : One (Word α) := ⟨⟨[]⟩⟩

@[simp] lemma toList_one : ((1 : Word α) : List α) = [] := rfl

instance : Semigroup (Word α) where
  mul_assoc := by
    intro w₁ w₂ w₃
    ext; simp [toList_mul, List.append_assoc]

instance : MulOneClass (Word α) where
  mul := (· * ·)
  one := 1
  one_mul := by
    intro w; ext; simp [toList_mul, List.nil_append]
  mul_one := by
    intro w; ext; simp [toList_mul, List.append_nil]

end Word

/-- Languages over an alphabet `α` are sets of words. -/
abbrev Lang (α : Type*) := Set (Word α)

@[simp] lemma mem_one_lang {α} {w : Word α} :
    w ∈ (1 : Lang α) ↔ w = 1 := Iff.rfl

@[simp] lemma mem_mul_lang {α} {L M : Lang α} {w : Word α} :
    w ∈ L * M ↔ ∃ u ∈ L, ∃ v ∈ M, u * v = w := Iff.rfl

/-- Left distributivity of concatenation over `sSup` for languages. -/
lemma mul_sSup_lang {α} (L : Lang α) (S : Set (Lang α)) :
    L * sSup S = ⨆ M ∈ S, L * M := by
  ext w; constructor
  · intro h
    rcases h with ⟨u, hu, v, hv, hmul⟩
    rcases hv with ⟨M, hMS, hvM⟩
    refine Set.mem_iUnion.2 ?_
    exact ⟨M, Set.mem_iUnion.2 ⟨hMS, ⟨u, hu, v, hvM, hmul⟩⟩⟩
  · intro h
    rcases Set.mem_iUnion.1 h with ⟨M, hM⟩
    rcases Set.mem_iUnion.1 hM with ⟨hMS, hw⟩
    rcases hw with ⟨u, hu, v, hv, hmul⟩
    refine ⟨u, hu, v, ?_, hmul⟩
    exact ⟨M, hMS, hv⟩

/-- Right distributivity of concatenation over `sSup` for languages. -/
lemma sSup_mul_lang {α} (S : Set (Lang α)) (L : Lang α) :
    sSup S * L = ⨆ M ∈ S, M * L := by
  ext w; constructor
  · intro h
    rcases h with ⟨u, hu, v, hv, hmul⟩
    rcases hu with ⟨M, hMS, huM⟩
    refine Set.mem_iUnion.2 ?_
    exact ⟨M, Set.mem_iUnion.2 ⟨hMS, ⟨u, huM, v, hv, hmul⟩⟩⟩
  · intro h
    rcases Set.mem_iUnion.1 h with ⟨M, hM⟩
    rcases Set.mem_iUnion.1 hM with ⟨hMS, hw⟩
    rcases hw with ⟨u, hu, v, hv, hmul⟩
    refine ⟨u, ?_, v, hv, hmul⟩
    exact ⟨M, hMS, hu⟩

/-- `Lang α` forms a quantale under union and concatenation. -/
instance instIsQuantaleLang (α : Type*) : IsQuantale (Lang α) where
  mul_sSup_distrib := mul_sSup_lang
  sSup_mul_distrib := sSup_mul_lang

/-- Quantale instance for languages over any alphabet `α`. -/
instance instQuantaleLang (α : Type*) : Quantale (Lang α) := {}

end LanguageQuantale
