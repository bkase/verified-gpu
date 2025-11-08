import Effects
import Kernel.Typing
import WGSL.AST

open Effects
open LanguageQuantale

namespace WGSL

structure AccessAst where
  space  : AddrSpace
  base   : String
  idx    : Expr
  guard  : Expr
  effect : Effects.Access
deriving Repr, DecidableEq

structure PhaseAst where
  reads  : List AccessAst := []
  writes : List AccessAst := []
  effect : Effects.Phase := {}
deriving Repr, DecidableEq

abbrev GradeAst := LanguageQuantale.Word PhaseAst

namespace GradeAst
@[inline] def ofRead (a : AccessAst) : GradeAst :=
  .ofList
    [ { reads := [a], writes := []
      , effect := { reads := [a.effect], writes := [] } } ]

@[inline] def ofWrite (a : AccessAst) : GradeAst :=
  .ofList
    [ { reads := [], writes := [a]
      , effect := { reads := [], writes := [a.effect] } } ]

@[inline] def ofBarrier : GradeAst :=
  .ofList
    [ { reads := [], writes := [], effect := { reads := [], writes := [] } }
    , { reads := [], writes := [], effect := { reads := [], writes := [] } } ]

@[inline] def seq (g h : GradeAst) : GradeAst := g * h
end GradeAst

@[inline] def guardAllExpr : WGSL.Expr :=
  WGSL.Expr.eq
    (WGSL.Expr.mod (WGSL.Expr.builtin .local_invocation_id_x) (WGSL.Expr.litU32 1))
    (WGSL.Expr.litU32 0)

@[inline] def stampAccess (a : AccessAst) (gExpr : WGSL.Expr) (gEff : Effects.Guard) :
    AccessAst :=
  { a with
      guard := gExpr
      effect := { a.effect with guard := gEff } }

@[inline] def stampPhase (p : PhaseAst) (gExpr : WGSL.Expr) (gEff : Effects.Guard) :
    PhaseAst :=
  { reads := p.reads.map (fun a => stampAccess a gExpr gEff)
  , writes := p.writes.map (fun a => stampAccess a gExpr gEff)
  , effect := Kernel.stampPhase p.effect gEff }

@[inline] def stampGrade (w : GradeAst) (gExpr : WGSL.Expr) (gEff : Effects.Guard) :
    GradeAst :=
  .ofList (w.toList.map (fun p => stampPhase p gExpr gEff))

@[inline] def eraseAccess (a : AccessAst) : Effects.Access :=
  a.effect

@[inline] def erasePhase (p : PhaseAst) : Effects.Phase :=
  p.effect

@[inline] def eraseGrade (g : GradeAst) : Effects.Grade :=
  LanguageQuantale.Word.ofList (g.toList.map erasePhase)

@[simp] lemma eraseGrade_one :
    eraseGrade (1 : GradeAst) = (1 : Effects.Grade) := rfl

@[simp] lemma eraseGrade_ofRead (a : AccessAst) :
    eraseGrade (GradeAst.ofRead a)
      = LanguageQuantale.Word.ofList [⟨[a.effect], []⟩] := rfl

@[simp] lemma eraseGrade_ofRead_effect (a : AccessAst) :
    eraseGrade (GradeAst.ofRead a) = Kernel.Grade.ofRead a.effect := by
  simp [Kernel.Grade.ofRead]

@[simp] lemma eraseGrade_ofWrite (a : AccessAst) :
    eraseGrade (GradeAst.ofWrite a)
      = LanguageQuantale.Word.ofList [⟨[], [a.effect]⟩] := rfl

@[simp] lemma eraseGrade_ofWrite_effect (a : AccessAst) :
    eraseGrade (GradeAst.ofWrite a) = Kernel.Grade.ofWrite a.effect := by
  simp [Kernel.Grade.ofWrite]

@[simp] lemma eraseGrade_ofBarrier :
    eraseGrade GradeAst.ofBarrier
      = LanguageQuantale.Word.ofList [⟨[], []⟩, ⟨[], []⟩] := rfl

@[simp] lemma eraseGrade_ofBarrier_effect :
    eraseGrade GradeAst.ofBarrier = Kernel.Grade.ofBarrier := by
  simp [Kernel.Grade.ofBarrier]

@[simp] lemma eraseGrade_seq (g h : GradeAst) :
    eraseGrade (GradeAst.seq g h) = eraseGrade g * eraseGrade h := by
  ext1
  simp [GradeAst.seq, eraseGrade, List.map_append, Word.toList_mul]

@[simp] lemma eraseGrade_mul (g h : GradeAst) :
    eraseGrade (g * h) = eraseGrade g * eraseGrade h := by
  simpa [GradeAst.seq] using eraseGrade_seq g h

end WGSL
