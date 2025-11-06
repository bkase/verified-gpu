import Kernel.Typing

namespace Tests

open Kernel
open Effects

def sampleWGLoc : Kernel.Loc :=
  { space := .workgroup
    base := "wgBuf"
    idx := {} }

def sampleStorageLoc : Kernel.Loc :=
  { space := .storage
    base := "stBuf"
    idx := {} }

def guardAlt : Guard := { step := 2, phase := 1 }

def sampleThreadsBody : Kernel.Stmt :=
  .seq (.load sampleWGLoc "thr") (.store sampleWGLoc (.var "thr"))

def sampleOffsets : List (Nat × Kernel.Stmt) :=
  [ (0, .load sampleStorageLoc "tmp")
  , (1, .store sampleStorageLoc (.var "tmp")) ]

def sampleStmt : Kernel.Stmt :=
  .seq .skip
    (.seq (.let_ "x" (.lit 0))
      (.seq (.load sampleWGLoc "tmp")
        (.seq (.store sampleWGLoc (.var "tmp"))
          (.seq (.atomicAdd sampleStorageLoc (.lit 1) "acc")
            (.seq (.ite guardAlt (.store sampleStorageLoc (.lit 42)))
              (.seq .barrier_wg
                (.seq (.for_threads sampleThreadsBody)
                  (.seq .barrier_st (.for_offsets sampleOffsets)))))))))

def readWG : Effects.Grade := Kernel.Grade.ofRead (Kernel.asRead sampleWGLoc Kernel.guardAll)
def writeWG : Effects.Grade := Kernel.Grade.ofWrite (Kernel.asWrite sampleWGLoc Kernel.guardAll)
def writeStorage : Effects.Grade := Kernel.Grade.ofWrite (Kernel.asWrite sampleStorageLoc Kernel.guardAll)
def readStorage : Effects.Grade := Kernel.Grade.ofRead (Kernel.asRead sampleStorageLoc Kernel.guardAll)
def gradeIte : Effects.Grade := Kernel.stampGrade writeStorage guardAlt
def gradeThreads : Effects.Grade := Kernel.Grade.seq readWG writeWG
def gradeOffsets : Effects.Grade := Kernel.Grade.seq readStorage writeStorage

def expectedGrade : Effects.Grade :=
  ([readWG, writeWG, gradeIte, Kernel.Grade.ofBarrier, gradeThreads, Kernel.Grade.ofBarrier, gradeOffsets]
    ).foldl Kernel.Grade.seq Kernel.Grade.eps

def expectedGradePhases : List Effects.Phase := expectedGrade.toList

def run : IO Unit := do
  let actual := (Kernel.gradeOf sampleStmt).toList
  if actual = expectedGradePhases then
    IO.println "gradeOf sampleStmt OK"
  else
    throw <| IO.userError s!"gradeOf mismatch.\nexpected: {repr expectedGradePhases}\nactual: {repr actual}"

#eval run

end Tests
