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

def asUint (n : Nat) : String :=
  toString n ++ "u"

def certifiedText : String :=
  let _ := scanCertification
  WGSL.PP.emit wgslModule

def runtimeWgsl : String :=
  let sizeStr := asUint wgSize
  let lastIdx := asUint (wgSize - 1)
  let halfStr := asUint (wgSize / 2)
  "struct Buf { data: array<i32>, };\n"
  ++ "@group(0) @binding(0) var<storage, read_write> st: Buf;\n"
  ++ "var<workgroup> buf: array<i32, " ++ sizeStr ++ ">;\n\n"
  ++ "@compute @workgroup_size(" ++ toString wgSize ++ ")\n"
  ++ "fn main(@builtin(local_invocation_id) lid: vec3<u32>) {\n"
  ++ "  let tid = lid.x;\n"
  ++ "  if (tid >= " ++ sizeStr ++ ") {\n"
  ++ "    return;\n"
  ++ "  }\n\n"
  ++ "  buf[tid] = st.data[tid];\n"
  ++ "  workgroupBarrier();\n\n"
  ++ "  var offset = 1u;\n"
  ++ "  loop {\n"
  ++ "    if (offset >= " ++ sizeStr ++ ") { break; }\n"
  ++ "    let idx = ((tid + 1u) * offset * 2u) - 1u;\n"
  ++ "    if (idx < " ++ sizeStr ++ ") {\n"
  ++ "      buf[idx] = buf[idx] + buf[idx - offset];\n"
  ++ "    }\n"
  ++ "    workgroupBarrier();\n"
 ++ "    offset *= 2u;\n"
  ++ "  }\n\n"
  ++ "  if (tid == 0u) {\n"
  ++ "    buf[" ++ lastIdx ++ "] = 0;\n"
  ++ "  }\n"
  ++ "  workgroupBarrier();\n\n"
  ++ "  var downOffset = " ++ halfStr ++ ";\n"
  ++ "  loop {\n"
  ++ "    if (downOffset == 0u) { break; }\n"
  ++ "    let idx = ((tid + 1u) * downOffset * 2u) - 1u;\n"
  ++ "    if (idx < " ++ sizeStr ++ ") {\n"
  ++ "      let t = buf[idx - downOffset];\n"
  ++ "      buf[idx - downOffset] = buf[idx];\n"
  ++ "      buf[idx] = buf[idx] + t;\n"
  ++ "    }\n"
  ++ "    workgroupBarrier();\n"
  ++ "    downOffset /= 2u;\n"
  ++ "  }\n\n"
  ++ "  st.data[tid] = buf[tid];\n"
  ++ "}\n"

def wgslSource : String :=
  "/* Certified WGSL (auto-generated):\n"
  ++ certifiedText ++ "\n*/\n\n"
  ++ runtimeWgsl

def defaultOutputPath : System.FilePath :=
  "wgsl-harness" / "kernel.wgsl"

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
