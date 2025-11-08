# VerifiedGPU: Graded-Effect Semantics for Race‑Free WebGPU Kernels (Lean 4)

**VerifiedGPU** is a Lean 4 project that formalizes a lightweight kernel model close to the WebGPU Shading Language (WGSL), and uses a **language quantale** to reason compositionally about absence of data races and about barrier placement. WGSL is the shading language for the modern web graphics standard called [WebGPU](https://en.wikipedia.org/wiki/WebGPU). The first target demonstration is a verified **Blelloch‑style scan** ([exclusive prefix sum](https://developer.nvidia.com/gpugems/gpugems3/part-vi-gpu-computing/chapter-39-parallel-prefix-sum-scan-cuda)) with workgroup barriers that are intended to be optimal, plus a path to certified WGSL emission.

- Quantale of languages: `Lang α := Set (Word α)` with concatenation and arbitrary joins
- GPU “phase alphabet”: `Phase` (reads/writes/guards/space)
- **Grades**: words over `Phase` (phase traces) with singleton **denotation** into the quantale
- Per-phase obligations: pairwise-disjoint writes (`WritesDisjointPhase`) and no read-after-write within a phase (`NoRAWIntraPhase`)
- Goal: Type-checking implies data-race freedom in workgroups; barriers adequate and, we hope, minimal
- WGSL backend: `WGSL.Codegen` lowers the IR to WGSL, proves grade preservation, and produces a certified kernel via `CertifiedEmit_wgScan`

---

## Table of Contents

1. [Why this exists](#why-this-exists)
2. [Getting started](#getting-started)
3. [Design in 90 seconds](#design-in-90-seconds)
4. [Typing rules](#typing-rules)
5. [Theorem spotlight: end-to-end data-race freedom for the concrete Blelloch scan](#theorem-spotlight-end-to-end-data-race-freedom-for-the-concrete-blelloch-scan)
   - [What the theorem says](#what-the-theorem-says)
   - [Why “up to normalization”?](#why-up-to-normalization)
   - [Where the pieces live (code map)](#where-the-pieces-live-code-map)
   - [Proof sketch and how the parts compose](#proof-sketch-and-how-the-parts-compose)
   - [How to reproduce / inspect in Lean](#how-to-reproduce--inspect-in-lean)

6. [Current status](#current-status)
7. [What’s next: WebGPU Shading Language emission and running on hardware](#whats-next-webgpu-shading-language-emission-and-running-on-hardware)
8. [References](#references)
9. [Appendix: Key definitions](#appendix-key-definitions-as-implemented)

---

## Why this exists

Kernels for graphics processing units are easy to get subtly wrong (missing barriers, aliasing writes, read‑after‑write hazards, and write‑after‑write hazards). Rather than ad‑hoc proofs, we:

- track **who reads/writes what, and when** (per **phase**),
- **split phases** at barriers,
- prove **pairwise disjointness** and **intra‑phase read‑after‑write safety**,
- lift into a **quantale** of phase traces for compositional laws,
- (soon) emit WGSL code matching the proven barrier structure.

What is the Blelloch scan? It is the classic work‑efficient parallel exclusive prefix‑sum that proceeds in two tree‑shaped passes over an array: an “upsweep” reduction to build partial sums, followed by a “downsweep” to produce exclusive prefixes; each level uses synchronization. It performs a total amount of work that scales linearly with the input size and has span that grows logarithmically with the input size. It is a standard primitive for graphics processing units. See the overview in GPU Gems 3, Chapter 39: [Parallel Prefix Sum (Scan) with CUDA](https://developer.nvidia.com/gpugems/gpugems3/part-vi-gpu-computing/chapter-39-parallel-prefix-sum-scan-cuda).

---

## Getting started

Toolchain is pinned in `lean-toolchain` (currently Lean 4.25 RC). Build and run everything via `lake` (mathlib required).

```bash
# optional: reproducible shell
direnv allow     # or: nix develop  /  devenv shell

# ensure toolchain
elan toolchain install $(cat lean-toolchain)
lake build
# default target only checks `LanguageQuantale`; build other libraries explicitly
lake build Effects   # phase alphabet + grades + normalization
lake build Kernel    # Syntax, Typing, Lemmas (e.g., affine facts)
lake build Tests     # sample programs / grade synthesis smoke tests
lake build WGSL      # WGSL AST + footprint + certified emitter

# run the executable kernel harness once proofs/build succeed
cargo test -p wgsl-harness --manifest-path wgsl-harness/Cargo.toml
```

### Running the WGSL harness

The Rust harness in `wgsl-harness/` uses `build.rs` to call `lake exe emitWGSL`
and drops the certified kernel at `wgsl-harness/.generated/kernel.wgsl`. Every
`cargo build`/`cargo test` automatically refreshes this artifact and exports the
absolute path via `WGSL_KERNEL_PATH`, so you do **not** need to run the Lean
emitter manually.

To execute the end-to-end GPU test (which uploads a 256-element array, runs the
certified scan, and checks the exclusive prefix sums), simply run:

```bash
cargo test --manifest-path wgsl-harness/Cargo.toml
```

Ensure you have a WebGPU-capable runtime (wgpu will fall back to software if
needed). The test named `computes_exclusive_scan` should pass and mirrors the
WGSL produced by the proofs.

Repository layout (high‑level):

```
LanguageQuantale.lean   -- Words and languages; quantale instances
Effects.lean            -- Phase alphabet for graphics processing units; grade operations, normalization, denotation; safety predicates
Kernel/                 -- Core intermediate representation close to the WGSL, and the typing judgment
  Syntax.lean           -- Expressions, locations, statements (abstract syntax tree)
  Typing.lean           -- Graded typing rules and synthesizer (`gradeOf`)
  Lemmas/               -- Reusable arithmetic and guard reasoning facts
    Affine.lean         -- Affine index lemmas for Blelloch‑style scans
  Examples/             -- Drop-in proof patterns for specific kernels
    Blelloch.lean       -- Upsweep/downsweep and end-to-end scan grade proofs
Tests/                  -- Quick grade synthesis checks
  GradeEval.lean        -- End-to-end sample touching every statement form
WGSL/                   -- WGSL AST, footprint/erasure logic, and certified emitter
  AST.lean              -- Minimal WGSL syntax + pretty-printer
  Footprint.lean        -- WGSL-side phases/grades with erasure into Effects.Grade
  Codegen.lean          -- IR → WGSL lowering, grade preservation, CertifiedEmit_wgScan
```

---

## Design in 90 seconds

- A **Phase** summarizes the _intra‑epoch_ memory footprint: `reads`, `writes` (each a list of `Access` with `space`, `base`, `idx : Aff2`, `guard`). A phase is the unit of reasoning between barriers.

- A **Grade** is a **word of phases** (a phase trace). Concretely, it is a sequence that records, in order, the abstract memory footprint that each epoch performs, with explicit barrier cuts. “Phase trace” means we track only the “who, where, and when” of memory actions (memory spaces, bases, indices, and guards) — not the computed values — and we keep the sequence boundaries that matter for synchronization. Barriers appear as a special separator that phases never cross.

- **Denotation** embeds a concrete grade as a singleton **language** `{word}` in the quantale `Lang Phase`. Why denotation? It gives an extensional meaning we can equate modulo normalization: two grades are “the same behavior” if their denotations (after normalization that fuses adjacent non‑empty phases but never crosses barriers) coincide. This avoids baking rewrite rules into syntax and lets us use set‑theoretic reasoning for joins and refinement.

- The **quantale** gives us exactly the algebra we need for compositional effect reasoning:
  - monoidal sequencing `⊗` for `;` (concatenate traces),
  - arbitrary joins `⋁` for branching/families (`if`, `for`, non‑det choice),
  - order `≤` for refinement (“implementation refines specification”),
  - distributivity `x ⊗ ⋁S = ⋁{x ⊗ s | s ∈ S}` so local reasoning composes through control‑flow. Using the language quantale (sets of words, concat, union) makes these properties immediate.

- The concurrency rule checks per phase:
  - `WritesDisjointPhase`: distinct threads never write the same combination of memory space, base, and address
  - `NoRAWIntraPhase`: within a single phase, a read does not alias any write

---

## Typing rules

Our typing judgment has the shape `Γ ⊢ s ▷ g`: “In environment `Γ`, statement `s` synthesizes grade `g`.” See `Kernel/Typing.lean` for constructors like:

- `g_for_threads` (parallel threads, data‑race‑freedom side‑conditions),
- `g_if_guard` (guard stamping),
- `g_seq`, `g_bar_wg`/`g_bar_st`, `g_load`, `g_store`, …

The synthesis function `gradeOf : Stmt → Effects.Grade` computes a conservative phase trace and is sound for the thread‑free fragment; the `for_threads` rule imposes the data‑race‑freedom side‑conditions via `PhasesSafe g`.

### Rule reference (inference form)

Abbreviations:

- `ε` = empty grade (`Grade.eps`)
- `g ⊙ h` = sequential composition (`Grade.seq g h`)
- `B(g)` = append a phase boundary (`g ⊙ Grade.ofBarrier`)
- `R(loc)` / `W(loc)` = singleton read/write footprints from `loc`
- `stamp(g,guard)` = attach `guard` to all accesses in `g`

**Basic constructs**

$$
\frac{\ }{\Gamma \vdash \texttt{skip} \triangleright \varepsilon}\quad\text{(T-Skip)}
$$

$$
\frac{\ }{\Gamma \vdash \texttt{let}\ x:=e \triangleright \varepsilon}\quad\text{(T-Let)}
$$

**Memory effects**

$$
\frac{\ }{\Gamma \vdash \texttt{load}\;loc\;dst \triangleright R(loc)}\quad\text{(T-Load)}
$$

$$
\frac{\ }{\Gamma \vdash \texttt{store}\;loc\;rhs \triangleright W(loc)}\quad\text{(T-Store)}
$$

$$
\frac{\ }{\Gamma \vdash \texttt{atomicAdd}\;loc\;rhs\;dst \triangleright \varepsilon}\quad\text{(T-Atomic)}
$$

**Composition and barriers**

$$
\frac{\Gamma \vdash s \triangleright g \quad \Gamma \vdash t \triangleright h}{\Gamma \vdash s ; t \triangleright g \odot h}\quad\text{(T-Seq)}
$$

$$
\frac{\ }{\Gamma \vdash \texttt{workgroupBarrier} \triangleright B(\varepsilon)}\quad\text{(T-Barrier-WG)}
$$

$$
\frac{\ }{\Gamma \vdash \texttt{storageBarrier} \triangleright B(\varepsilon)}\quad\text{(T-Barrier-ST)}
$$

**Guards and families**

$$
\frac{\Gamma \vdash s \triangleright g}{\Gamma \vdash \texttt{if}\ (guard)\ \{s\} \triangleright stamp(g,\,guard)}\quad\text{(T-IfGuard)}
$$

$$
\frac{\ }{\Gamma \vdash \texttt{for\\_offsets}\;[] \triangleright \varepsilon}\quad\text{(T-ForOffsets-Nil)}
$$

$$
\frac{\Gamma \vdash s \triangleright g_1 \quad \Gamma \vdash \texttt{for\\_offsets}\;ks \triangleright g_2}{\Gamma \vdash \texttt{for\\_offsets}\;((k,s)::ks) \triangleright g_1 \odot g_2}\quad\text{(T-ForOffsets-Cons)}
$$

**Parallel threads (crux)**

$$
\frac{\Gamma \vdash body \triangleright g \quad \forall p \in \mathrm{phases}(g),\;\mathrm{WritesDisjointPhase}(p) \wedge \mathrm{NoRAWIntraPhase}(p)}{\Gamma \vdash \texttt{for\\_threads}\ \{body\} \triangleright g}\quad\text{(T-ForThreads)}
$$

- `phases(g)` is `Grade.phases g` (exposed in Lean for the side-condition)
- `WritesDisjointPhase` / `NoRAWIntraPhase` come from `Effects.lean`

### How typing yields absence of data races

Typing is not just bookkeeping — it enforces absence of data races:

- `gradeOf s = g` summarizes `s` as a phase trace with explicit barriers.
- To type `.for_threads s`, rule `g_for_threads` requires `PhasesSafe g`.
- `PhasesSafe g` packages per‑phase obligations: `WritesDisjointPhase` and the “no read‑after‑write within a phase” predicate `NoRAWIntraPhase` for every phase in `g`.
- Barriers in `g` split epochs; safety is required within phases, and barriers provide the happens‑before relation between phases.
- Therefore, if `Γ ⊢ .for_threads s ▷ g` holds, then running `s` in parallel workgroup threads has no data races within each epoch and between epochs separated by barriers.

---

## Theorem spotlight: end-to-end data-race freedom for the concrete Blelloch scan

### What the theorem says

At the heart of the repository we now have the following end-to-end result for the **concrete intermediate representation** of the workgroup Blelloch scan:

```lean
lemma hasGrade_forThreads_wgScanStmt_upToNorm {Γ} (offs) :
  HasGrade Γ (.for_threads (wgScanStmt offs))
           (gradeOf (wgScanStmt offs))
  ∧ gradeOf (wgScanStmt offs) ≈ wgScanGrade offs :=
⟨ hasGrade_forThreads_wgScanStmt (Γ := Γ) (offs := offs)
 , wgScanStmt_upToNorm offs ⟩
```

Plain language summary. For any nonempty list of strictly positive offsets `offs` (the usual Blelloch schedule), the concrete statement `wgScanStmt offs`:

1. Type‑checks under `for_threads` with synthesized grade `gradeOf (wgScanStmt offs)`. Type‑checking via `HasGrade …` enforces the per‑phase data‑race‑freedom side‑conditions (pairwise‑disjoint writes and no read‑after‑write within a phase), so the kernel is race‑free by construction between consecutive barriers.

2. The synthesized grade, when interpreted up to normalization (`≈` denotes equality of singleton denotations), is extensionally equal to the abstract specification grade `wgScanGrade offs`. In other words, the barrier structure and read/write footprints of the actual intermediate‑representation implementation coincide with the specification after fusing runs of non‑empty phases (but never across explicit barrier cuts).

Combined, this is a full “implementation refines specification” plus “absence of data races” result: the concrete Blelloch scan that we will emit to the WebGPU Shading Language is provably race‑free, with the intended barrier placement and no hidden phase reordering beyond deterministic normalization.

### Why “up to normalization”?

Grades are words of phases; we make normalization explicit so that proofs never smuggle rewrites into sequencing. Normalization (`Effects.Grade.normalize`) only

- **fuses adjacent non‑empty phases**,
- **never** crosses explicit barrier pairs `[⟨[],[]⟩, ⟨[],[]⟩]` (see `normalizeList_barrier_*` lemmas).

Thus `g ≈ h` means `{normalize g} = {normalize h}` as languages. This gives the right extensionality notion for “same phase trace modulo trivial chunking”, while keeping barrier cuts **hard**.

### Where the pieces live (code map)

- **Intermediate representation of the scan (concrete program):**
  `Kernel/Examples/Blelloch.lean` → `namespace WG.IR` (here `IR` is short for “intermediate representation”)
  - `wgScanStmt` : builds the sequence of upsweeps, then downsweeps, each ending in a barrier.
  - `gradeOf_wgScanStmt` : computes its grade by syntax‑directed synthesis.

- **Specification grade (abstract target):**
  `Kernel/Examples/Blelloch.lean` → `namespace WG`
  - `wgScanGrade` : `gradeUpsweeps offs ⋆ gradeDownsweeps offs`.
  - `wgScanGrade_safe` : all phases in the specification are proven safe for absence of data races.

- **Bridging IR ↔ Spec (normalization and safety):**
  - `WG.IR.wgScanGradeIR_normalizes` : the IR grade normalizes to the spec grade.
  - `WG.IR.wgScanGradeIR_safe` : phases of the IR grade are proven safe for absence of data races.
  - `gradeUpsweepIR_normalizes`, `gradeDownsweepIR_normalizes` : per‑stage equalities.

- **Arithmetic and affine lemmas discharging the obligations for absence of data races:**
  `Kernel/Lemmas/Affine.lean`
  - `upsweep_index_distinct`, `downsweep_index_distinct_both`, …
  - Guard reasoning: `upsweep_guard_mixed_targets_ne`, and related lemmas.

- **Concurrency rule and the data‑race‑freedom check:**
  `Kernel/Typing.lean`
  - `HasGrade.g_for_threads` : requires `PhasesSafe g`.
  - `PhasesSafe.seq`, `PhasesSafe.barrier` : compositional safety facts.

- **Final statement (this spotlight):**
  `Kernel/Examples/Blelloch.lean` → bottom of `namespace WG.IR`
  - `hasGrade_forThreads_wgScanStmt_upToNorm` (the two‑part conjunction).

### Proof sketch and how the parts compose

**Pipeline (conceptual):**

```
          (concrete intermediate representation)     (abstract specification)
         wgScanStmt offs           ─────→               wgScanGrade offs
              │                                          ▲
              │ gradeOf (syntax‑directed)                 │  normalization equality
              ▼                                          │  (no barrier crossing)
         gradeOf (wgScanStmt offs)  ──── normalize ──────┘

and, independently:

   HasGrade Γ (wgScanStmt offs) (gradeOf …)     ∧     PhasesSafe (gradeOf …)
      └── by `g_for_threads` plus lemmas establishing absence of data races (affine reasoning per phase)
```

1. **Compute grades:** `gradeOf` over the concrete intermediate representation (`wgScanStmt`) produces a grade whose list form is a concatenation of (guarded read/write phases) each followed by an explicit barrier.

2. **Local collapses:** At each stage, we show that the two consecutive non‑empty phases fuse to the single abstract stage under list‑level normalization (`normalizeList_stage_pair`). This yields `gradeUpsweepIR_normalizes` and `gradeDownsweepIR_normalizes`.

3. **Global collapse:** Using the “cut at the barrier” lemmas
   (`normalizeList_barrier_middle_append`, `…_append_barrier_right`) we normalize the whole IR word into the abstract word:
   `wgScanGradeIR_normalizes` and then `gradeOf_wgScanStmt_normalizes`.

4. **Obligations for absence of data races:** For each phase we discharge
   `WritesDisjointPhase` and the “no read‑after‑write within a phase” predicate `NoRAWIntraPhase` using the affine lemmas (`Kernel/Lemmas/Affine.lean`), packaged into `…_safe` lemmas for upsweeps, downsweeps, and the whole scan. This gives `PhasesSafe (gradeOf …)`.

5. **Concurrency rule:** With `PhasesSafe` in hand, apply `HasGrade.g_for_threads` to obtain
   `HasGrade Γ (.for_threads (wgScanStmt offs)) (gradeOf …)`.

6. **Combine:** Conjoin the `HasGrade` judgment with the normalization equality to the specification:
   `hasGrade_forThreads_wgScanStmt_upToNorm`.

**What this buys us.** The concrete implementation has:

- **Correct barrier structure** (explicit and preserved),
- **Per‑phase absence of data races** when executed in parallel under `for_threads`,
- **Behavioral equality** (up to normalization) to the abstract scan grade.

### How to reproduce / inspect in Lean

A few helpful commands while browsing the files:

```lean
-- In Kernel/Examples/Blelloch.lean
#check WG.IR.wgScanStmt
#check WG.wgScanGrade
#check WG.IR.hasGrade_forThreads_wgScanStmt
#check wgScanStmt_upToNorm
#check hasGrade_forThreads_wgScanStmt_upToNorm

-- Inspect normalization lemmas for single stages:
#check WG.IR.gradeUpsweepIR_normalizes
#check WG.IR.gradeDownsweepIR_normalizes

-- Inspect safety facts:
#check WG.IR.wgScanGradeIR_safe
#check Kernel.PhasesSafe.barrier
#check Kernel.Lemmas.upsweep_index_distinct

-- WGSL backend and certificate (WGSL/Codegen.lean)
#check WGSL.buildModule
#check WGSL.PP.emit
#check WGSL.CertifiedEmit_wgScan
#eval WGSL.PP.emit (WGSL.buildModule default (Kernel.Examples.WG.IR.wgScanStmt [1,2,4,8]))
```

To build everything:

```bash
lake build Kernel
```

---

## Current status

- **Normalizer fixed points (lists):** Abstract upsweep and downsweep chains are fixed points of `normalizeList`. See `gradeUpsweeps_normal_list` and `gradeDownsweeps_normal_list`.
- **Barrier‑cut lemmas:** `normalizeList_barrier*` ensures runs of non‑empty phases fuse but never cross explicit barrier pairs.
- **Equivalence between specification and intermediate representation:** The grade of the full scan in the IR normalizes to the spec grade (`wgScanGradeIR_normalizes`, `gradeOf_wgScanStmt_normalizes`).
- **Discharging the obligations for absence of data races:** Per-phase `WritesDisjointPhase` and `NoRAWIntraPhase` are proven using affine index facts (`Kernel/Lemmas/Affine.lean`), packaged as `…_safe` lemmas.
- **New end-to-end result:**
  `hasGrade_forThreads_wgScanStmt_upToNorm` (in `Kernel/Examples/Blelloch.lean`) establishes that the concrete Blelloch scan in the intermediate representation, when run under `for_threads`, synthesizes a grade whose normalized denotation equals the specification grade, and the `HasGrade` judgment ensures absence of data races per phase. This is the core certification that the implementation is race-free with the intended barriers.
- **Certified WGSL emission:** `WGSL.Codegen` lowers `Kernel.Stmt` programs to a tiny WGSL subset, proves grade erasure preserves `Kernel.gradeOf`, and packages the existing scan proof into `CertifiedEmit_wgScan`. That theorem states the emitted WGSL for `wgScanStmt offs` is race-free (via `HasGrade`) and its grade matches the spec up to normalization, giving a turnkey artifact for downstream tooling.

---

## What’s next: WebGPU Shading Language emission and running on hardware

With the core absence‑of‑data‑races and normalization story in place, the remaining steps are mechanical and pave the path to execution:

1. **Host scaffolding and execution:** Provide a small runtime to upload buffers, dispatch the certified WGSL kernel (`WGSL.PP.emit (WGSL.buildModule …)`), and validate results (for example, compare against a CPU scan).

2. **Pipeline integration / artifacts:** Hook the emitter into the build so a concrete WGSL file (and maybe SPIR-V) is produced alongside the Lean proof, making it easy to feed into `wgpu`/`naga` tooling.

3. **(Optional) Minimality:** Prove that removing any barrier in the specification or the intermediate representation increases the normalized word or introduces a data race (barrier optimality).

---

## References

- Atkey, **Parameterised Notions of Computation** (graded/parameterised monads)
- Quantales for effect semantics; languages over free monoids
- Blelloch, **Prefix Sums and Their Applications** (work‑efficient scans)

---

## Appendix: Key definitions (as implemented)

- `Lang α := Set (Word α)` with `Quantale` instance (concat distributes over `sSup`)
- `Phase` (alphabet): `reads : List Access`, `writes : List Access`
- `Grade := Word Phase`
  - `seq : Grade → Grade → Grade`, `barrier : Grade → Grade`,
    `normalize : Grade → Grade`, `denote : Grade → Lang Phase`
  - lemmas: `toList_normalize`, `normalizeList_stage_pair`, `normalizeList_barrier_*`

- Obligations:
  - `WritesDisjointPhase : Phase → Prop`
  - `NoRAWIntraPhase    : Phase → Prop`

- Concurrency rule:
  - `HasGrade.g_for_threads : (∀ p ∈ phases g, …) → HasGrade Γ (.for_threads body) g`

---

_Pointers for code archeology_

- `LanguageQuantale.lean`: words, languages, quantale instances
- `Effects.lean`: `Phase`, `Access`, `Guard`, `Grade`, normalization, safety predicates
- `Kernel/Syntax.lean`: abstract syntax tree for the intermediate representation (expressions, loads/stores, guards, barriers, loops)
- `Kernel/Typing.lean`: typing rules, synthesis `gradeOf`, `PhasesSafe`
- `Kernel/Lemmas/Affine.lean`: arithmetic facts for disjointness under guards
- `Kernel/Examples/Blelloch.lean`: specification and intermediate representation of the Blelloch scan, normalization and absence‑of‑data‑races proofs (including the spotlight lemma)
From there, the WGSL backend reuses the exact same inhabitant: `CertifiedEmit_wgScan` (in `WGSL/Codegen.lean`) states that the pretty-printed WGSL module produced from `wgScanStmt offs` carries the erased grade of the IR proof and that grade still matches the spec up to normalization. In short, the code you can hand to a WebGPU runtime is the one that satisfies the theorem above.
