/-
  Kernel/Syntax.lean
  Minimal WGSL-like core IR that reuses Effects.{Space,Guard,Aff2}.
-/
import Effects

namespace Kernel

open Effects

/-- Arithmetic expressions (lightweight; extend as needed). -/
inductive Expr
| lit  : Int → Expr
| var  : String → Expr
| add  : Expr → Expr → Expr
| sub  : Expr → Expr → Expr
| mul  : Expr → Expr → Expr
| tidx : Expr                         -- current thread id (as Int)
deriving Repr, DecidableEq

/-- Pointer-like location: address space + base symbol + affine index. -/
structure Loc where
  space : Space
  base  : String
  idx   : Aff2
deriving Repr, DecidableEq

/-- WGSL-like statements (no types yet; we only care about memory effects & barriers). -/
inductive Stmt
| skip
| let_      : (name : String) → Expr → Stmt
| load      : (loc : Loc) → (dst : String) → Stmt
| store     : (loc : Loc) → (rhs : Expr) → Stmt
| atomicAdd : (loc : Loc) → (rhs : Expr) → (dst : String) → Stmt
| seq       : Stmt → Stmt → Stmt
| ite       : (guard : Guard) → (body : Stmt) → Stmt               -- activates subset of threads
| barrier_wg
| barrier_st
| for_threads : (body : Stmt) → Stmt                               -- run body for all tids in a WG
| for_offsets : List (Nat × Stmt) → Stmt                           -- finite unrolled family
deriving Repr

infixr:60 " ;; " => Stmt.seq

end Kernel
