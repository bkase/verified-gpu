import Std

namespace WGSL

inductive AddrSpace | workgroup | storage deriving DecidableEq, Repr
inductive ScalarTy | i32 | u32 deriving DecidableEq, Repr
inductive Builtin | local_invocation_id_x deriving DecidableEq, Repr

inductive Expr
| litI32  : Int → Expr
| litU32  : Nat → Expr
| var     : String → Expr
| builtin : Builtin → Expr
| add     : Expr → Expr → Expr
| sub     : Expr → Expr → Expr
| mul     : Expr → Expr → Expr
| mod     : Expr → Expr → Expr
| eq      : Expr → Expr → Expr
| castI32 : Expr → Expr
| castU32 : Expr → Expr
deriving DecidableEq, Repr

inductive Stmt
| skip
| let_      : String → Expr → Stmt
| load      : (arr : String) → (idx : Expr) → (dst : String) → Stmt
| store     : (arr : String) → (idx : Expr) → (rhs : Expr) → Stmt
| atomicAdd : (arr : String) → (idx : Expr) → (rhs : Expr) → (dst : String) → Stmt
| seq       : Stmt → Stmt → Stmt
| iff       : Expr → Stmt → Stmt
| workgroupBarrier
| storageBarrier
deriving Repr, Inhabited

infixr:60 " ;; " => Stmt.seq

structure Module where
  workgroupSize     : Nat := 256
  workgroupArrayLen : Nat := 256
  storageVar        : String := "st"
  workgroupVar      : String := "buf"
  body              : Stmt
deriving Repr

namespace PP
open WGSL

partial def ppE : Expr → String
| .litI32 z => s!"{z}"
| .litU32 n => s!"{n}u"
| .var x => x
| .builtin .local_invocation_id_x => "lid.x"
| .add a b => s!"({ppE a} + {ppE b})"
| .sub a b => s!"({ppE a} - {ppE b})"
| .mul a b => s!"({ppE a} * {ppE b})"
| .mod a b => s!"({ppE a} % {ppE b})"
| .eq a b  => s!"({ppE a} == {ppE b})"
| .castI32 e => s!"i32({ppE e})"
| .castU32 e => s!"u32({ppE e})"

partial def ppS : Stmt → List String
| .skip => []
| .let_ x e => [s!"let {x} = {ppE e};"]
| .load a i d => [s!"let {d} = {a}[{ppE i}];"]
| .store a i r => [s!"{a}[{ppE i}] = {ppE r};"]
| .atomicAdd a i r d => [s!"let {d} = atomicAdd(&{a}[{ppE i}], {ppE r});"]
| .seq s t => ppS s ++ ppS t
| .iff g b =>
    let body := (ppS b).map (fun ln => "  " ++ ln)
    [s!"if ({ppE g}) " ++ "{"] ++ body ++ ["}"]
| .workgroupBarrier => ["workgroupBarrier();"]
| .storageBarrier   => ["storageBarrier();"]

def emit (m : Module) : String :=
  let hdr :=
    "struct Buf { data: array<i32>, };\n" ++
    s!"@group(0) @binding(0) var<storage, read_write> {m.storageVar}: Buf;\n" ++
    s!"var<workgroup> {m.workgroupVar}: array<i32, {m.workgroupArrayLen}u>;\n"
  let entry :=
    s!"@compute @workgroup_size({m.workgroupSize})\n" ++
    s!"fn main(@builtin(local_invocation_id) lid: vec3<u32>) " ++ "{\n"
  hdr ++ "\n" ++ entry ++ String.intercalate "\n" (ppS m.body) ++ "\n}\n"
end PP

end WGSL
