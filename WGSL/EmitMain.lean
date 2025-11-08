import WGSL.Codegen
import Kernel.Examples.Blelloch

open Kernel
open Kernel.Examples

namespace WGSL

/-
Emit the certified Blelloch scan WGSL module, defaulting to
`wgsl-harness/kernel.wgsl` but accepting an optional CLI path override.
The offsets correspond to a single 256-thread workgroup (`[1,2,...,128]`).
-/

def defaultOffsets : List Nat :=
  [1, 2, 4, 8, 16, 32, 64, 128]

def wgSize : Nat := 256

def emitEnv : Env :=
  { bases :=
      [ { base := "buf", name := "buf", space := .workgroup }
      , { base := "st",  name := "st.data", space := .storage }
      ]
  , workgroupSize := wgSize
  , workgroupArrayLen := wgSize
  , storageVarName := "st"
  , workgroupVarName := "buf"
  , needsLastZero := true
  }

def wgScanStmt : Kernel.Stmt :=
  WG.IR.wgScanStmt defaultOffsets

def scanCertification :
    HasGrade { dummy := () }
      (.for_threads wgScanStmt)
      (eraseGrade (gradeOfGen emitEnv wgScanStmt))
  ∧ eraseGrade (gradeOfGen emitEnv wgScanStmt)
      ≈ WG.wgScanGrade defaultOffsets :=
  WGSL.CertifiedEmit_wgScan (Γ := { dummy := () }) emitEnv defaultOffsets

def wgslModule : Module :=
  WGSL.buildModule emitEnv wgScanStmt

def certifiedText : String :=
  let _ := scanCertification
  WGSL.PP.emit wgslModule

def wgslSource : String :=
  "/* Certified WGSL (auto-generated):\n"
  ++ certifiedText ++ "\n*/\n\n"
  ++ certifiedText

def defaultOutputPath : System.FilePath :=
  "wgsl-harness" / ".generated" / "kernel.wgsl"

def emitWGSLTo (path : System.FilePath) : IO Unit := do
  match path.parent with
  | some dir => IO.FS.createDirAll dir
  | none => pure ()
  IO.FS.writeFile path wgslSource
  IO.println s!"Wrote WGSL to {path}"

def emitMain (path? : Option System.FilePath := none) : IO Unit := do
  IO.println s!"Offsets: {defaultOffsets}"
  let target := path?.getD defaultOutputPath
  emitWGSLTo target

end WGSL

def main (args : List String) : IO UInt32 := do
  let target? :=
    match args with
    | out :: _ => some ⟨out⟩
    | _ => none
  WGSL.emitMain target?
  pure 0
