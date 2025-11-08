import Kernel.Typing
import Kernel.Examples.Blelloch
import WGSL.AST
import WGSL.Footprint

open Kernel
open Effects
open LanguageQuantale

namespace WGSL

structure BaseBinding where
  base  : String := ""
  name  : String := ""
  space : Effects.Space := .workgroup
deriving Repr, DecidableEq

instance : Inhabited BaseBinding :=
  ⟨{ base := "", name := "", space := .workgroup }⟩

structure Env where
  bases : List BaseBinding := []
  workgroupSize     : Nat := 256
  workgroupArrayLen : Nat := 256
  storageVarName    : String := "st"
  workgroupVarName  : String := "buf"
  needsLastZero     : Bool := false
deriving Repr

instance : Inhabited Env :=
  ⟨{ bases := [{ base := "buf", name := "buf", space := .workgroup }] }⟩

@[inline] def Env.lookup? (env : Env) (base : String) : Option BaseBinding :=
  env.bases.find? (fun b => b.base = base)

@[inline] def Env.lookup! (env : Env) (base : String) : BaseBinding :=
  match env.lookup? base with
  | some b => b
  | none => panic! s!"missing base binding for {base}"

@[inline] def cgSpace : Effects.Space → WGSL.AddrSpace
| .workgroup => .workgroup
| .storage   => .storage

@[inline] def tidU : WGSL.Expr := WGSL.Expr.builtin .local_invocation_id_x

@[inline] def cgIdx (a : Effects.Aff2) : WGSL.Expr :=
  let scaled := WGSL.Expr.mul (WGSL.Expr.castI32 tidU) (WGSL.Expr.litI32 a.a_tid)
  WGSL.Expr.castU32 (WGSL.Expr.add scaled (WGSL.Expr.litI32 a.b))

@[inline] def cgGuard (g : Effects.Guard) : WGSL.Expr :=
  WGSL.Expr.eq
    (WGSL.Expr.mod tidU (WGSL.Expr.litU32 g.step))
    (WGSL.Expr.litU32 g.phase)

@[inline] def cgLoc (env : Env) (loc : Kernel.Loc) : (WGSL.AddrSpace × String × WGSL.Expr) :=
  let binding := env.lookup! loc.base
  (cgSpace loc.space, binding.name, cgIdx loc.idx)

def cgExpr : Kernel.Expr → WGSL.Expr
| .lit z   => .litI32 z
| .var x   => .var x
| .add a b => .add (cgExpr a) (cgExpr b)
| .sub a b => .sub (cgExpr a) (cgExpr b)
| .mul a b => .mul (cgExpr a) (cgExpr b)
| .tidx    => .castI32 tidU

partial def cgStmt (env : Env) : Kernel.Stmt → WGSL.Stmt
| .skip => .skip
| .let_ x e => .let_ x (cgExpr e)
| .load loc dst =>
    let (_, name, idx) := cgLoc env loc
    .load name idx dst
| .store loc rhs =>
    let (_, name, idx) := cgLoc env loc
    .store name idx (cgExpr rhs)
| .atomicAdd loc rhs dst =>
    let (_, name, idx) := cgLoc env loc
    .atomicAdd name idx (cgExpr rhs) dst
| .seq s t => .seq (cgStmt env s) (cgStmt env t)
| .ite g body => .iff (cgGuard g) (cgStmt env body)
| .barrier_wg => .workgroupBarrier
| .barrier_st => .storageBarrier
| .for_threads body => cgStmt env body
| .for_offsets items =>
    items.foldr (fun ⟨_, body⟩ acc => .seq (cgStmt env body) acc) .skip

mutual
  def gradeOfGen (env : Env) : Kernel.Stmt → GradeAst
  | .skip => 1
  | .let_ _ _ => 1
  | .load loc _ =>
      let binding := env.lookup! loc.base
      GradeAst.ofRead
        { space := cgSpace loc.space
        , base  := binding.name
        , idx   := cgIdx loc.idx
        , guard := guardAllExpr
        , effect := Kernel.asRead loc Kernel.guardAll }
  | .store loc _ =>
      let binding := env.lookup! loc.base
      GradeAst.ofWrite
        { space := cgSpace loc.space
        , base  := binding.name
        , idx   := cgIdx loc.idx
        , guard := guardAllExpr
        , effect := Kernel.asWrite loc Kernel.guardAll }
  | .atomicAdd _ _ _ => 1
  | .seq s t => GradeAst.seq (gradeOfGen env s) (gradeOfGen env t)
  | .ite g body => stampGrade (gradeOfGen env body) (cgGuard g) g
  | .barrier_wg => GradeAst.ofBarrier
  | .barrier_st => GradeAst.ofBarrier
  | .for_threads body => gradeOfGen env body
  | .for_offsets items => gradeOfGenOffsets env items

def gradeOfGenOffsets (env : Env) : List (Nat × Kernel.Stmt) → GradeAst
  | [] => 1
  | ⟨_, body⟩ :: rest =>
      GradeAst.seq (gradeOfGen env body) (gradeOfGenOffsets env rest)
end

lemma erasePhase_stampPhase (p : PhaseAst) (gExpr : WGSL.Expr) (gEff : Effects.Guard) :
    erasePhase (stampPhase p gExpr gEff)
      = Kernel.stampPhase (erasePhase p) gEff := by
  simp [erasePhase, stampPhase]

lemma eraseGrade_stampGrade (w : GradeAst) (gExpr : WGSL.Expr) (gEff : Effects.Guard) :
    eraseGrade (stampGrade w gExpr gEff)
      = Kernel.stampGrade (eraseGrade w) gEff := by
  simp [stampGrade, Kernel.stampGrade, eraseGrade, erasePhase_stampPhase, List.map_map,
    Function.comp]

mutual
  theorem cg_preserves_grade (env : Env) :
      ∀ s, eraseGrade (gradeOfGen env s) = Kernel.gradeOf s
  | .skip => by simp [gradeOfGen, Kernel.gradeOf, eraseGrade, Kernel.Grade.eps]
  | .let_ _ _ => by simp [gradeOfGen, Kernel.gradeOf, eraseGrade, Kernel.Grade.eps]
  | .load loc _ => by
      simpa [ gradeOfGen
            , Kernel.gradeOf
            , Kernel.asRead
            , Kernel.guardAll
            , guardAllExpr ] using
        (eraseGrade_ofRead_effect
          { space := cgSpace loc.space
          , base := (env.lookup! loc.base).name
          , idx := cgIdx loc.idx
          , guard := guardAllExpr
          , effect := Kernel.asRead loc Kernel.guardAll })
  | .store loc _ => by
      simpa [ gradeOfGen
            , Kernel.gradeOf
            , Kernel.asWrite
            , Kernel.guardAll
            , guardAllExpr ] using
        (eraseGrade_ofWrite_effect
          { space := cgSpace loc.space
          , base := (env.lookup! loc.base).name
          , idx := cgIdx loc.idx
          , guard := guardAllExpr
          , effect := Kernel.asWrite loc Kernel.guardAll })
  | .atomicAdd _ _ _ => by simp [gradeOfGen, Kernel.gradeOf, eraseGrade, Kernel.Grade.eps]
  | .seq s t => by
      have hs := cg_preserves_grade env s
      have ht := cg_preserves_grade env t
      simp [gradeOfGen, Kernel.gradeOf, GradeAst.seq, Kernel.Grade.seq, hs, ht]
  | .ite g body => by
      have hb := cg_preserves_grade env body
      simp [gradeOfGen, Kernel.gradeOf, eraseGrade_stampGrade, hb]
  | .barrier_wg => by
      simpa [gradeOfGen, Kernel.gradeOf] using eraseGrade_ofBarrier_effect
  | .barrier_st => by
      simpa [gradeOfGen, Kernel.gradeOf] using eraseGrade_ofBarrier_effect
  | .for_threads body => cg_preserves_grade env body
  | .for_offsets items => cg_preserves_grade_offsets env items

  theorem cg_preserves_grade_offsets (env : Env) :
      ∀ items,
        eraseGrade (gradeOfGenOffsets env items)
          = Kernel.gradeOfOffsets items
  | [] => by simp [gradeOfGenOffsets, Kernel.gradeOfOffsets, eraseGrade, Kernel.Grade.eps]
  | ⟨_, body⟩ :: rest => by
      have hb := cg_preserves_grade env body
      have hrest := cg_preserves_grade_offsets env rest
      simp [gradeOfGenOffsets, Kernel.gradeOfOffsets, GradeAst.seq,
        Kernel.Grade.seq, hb, hrest]
end

@[simp] lemma eraseGrade_for_threads (env : Env) (s : Kernel.Stmt) :
    eraseGrade (gradeOfGen env (.for_threads s))
      = eraseGrade (gradeOfGen env s) := by rfl

@[simp] lemma eraseGrade_for_offsets (env : Env) (items) :
    eraseGrade (gradeOfGen env (.for_offsets items))
      = eraseGrade (gradeOfGenOffsets env items) := rfl

lemma emit_grade_eq_IR (env : Env) (offs : List Nat) :
    eraseGrade (gradeOfGen env (Kernel.Examples.WG.IR.wgScanStmt offs))
      = Kernel.gradeOf (Kernel.Examples.WG.IR.wgScanStmt offs) := by
  simpa using cg_preserves_grade env (Kernel.Examples.WG.IR.wgScanStmt offs)

/-- Assemble a WGSL module from an IR statement. -/
def buildModule (env : Env) (s : Kernel.Stmt) : Module :=
  let stArr := env.storageVarName ++ ".data"
  let wgArr := env.workgroupVarName
  let tid := tidU
  let copyIn :=
    WGSL.Stmt.seq
      (WGSL.Stmt.load stArr tid "_in")
      (WGSL.Stmt.store wgArr tid (WGSL.Expr.var "_in"))
  let copyOut :=
    WGSL.Stmt.seq
      (WGSL.Stmt.load wgArr tid "_out")
      (WGSL.Stmt.store stArr tid (WGSL.Expr.var "_out"))
  let zeroLast : WGSL.Stmt :=
    let lastIdx := WGSL.Expr.litU32 (env.workgroupArrayLen - 1)
    WGSL.Stmt.seq
      (WGSL.Stmt.iff (WGSL.Expr.eq tid (WGSL.Expr.litU32 0))
        (WGSL.Stmt.store wgArr lastIdx (WGSL.Expr.litI32 0)))
      WGSL.Stmt.workgroupBarrier
  let core :=
    if env.needsLastZero then
      match s with
      | Kernel.Stmt.seq ups downs =>
          WGSL.Stmt.seq (cgStmt env ups)
            (WGSL.Stmt.seq zeroLast (cgStmt env downs))
      | _ =>
          WGSL.Stmt.seq (cgStmt env s) zeroLast
    else
      cgStmt env s
  let body :=
    WGSL.Stmt.seq copyIn
      (WGSL.Stmt.seq WGSL.Stmt.workgroupBarrier
        (WGSL.Stmt.seq core
          (WGSL.Stmt.seq WGSL.Stmt.workgroupBarrier copyOut)))
  { workgroupSize := env.workgroupSize
  , workgroupArrayLen := env.workgroupArrayLen
  , storageVar := env.storageVarName
  , workgroupVar := env.workgroupVarName
  , body := body }

open Kernel.Examples

lemma emit_grade_eq_IR_wgScan (env : Env) (offs : List Nat) :
    eraseGrade (gradeOfGen env (WG.IR.wgScanStmt offs))
      = Kernel.gradeOf (WG.IR.wgScanStmt offs) :=
  emit_grade_eq_IR env offs

/-- Certified WGSL emission for the Blelloch scan. -/
theorem CertifiedEmit_wgScan {Γ} (env : Env) (offs : List Nat) :
    let s := WG.IR.wgScanStmt offs;
    HasGrade Γ (.for_threads s) (eraseGrade (gradeOfGen env s)) ∧
    eraseGrade (gradeOfGen env s) ≈ WG.wgScanGrade offs := by
  classical
  intro s
  have ⟨hHas, hUpTo⟩ := WG.IR.hasGrade_forThreads_wgScanStmt_upToNorm (Γ := Γ) offs
  have hPres := emit_grade_eq_IR env offs
  refine ⟨?_, ?_⟩
  · simpa [s, hPres.symm] using hHas
  · simp [s, hPres, Effects.Grade.denote]

end WGSL
