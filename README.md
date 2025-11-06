# VerifiedGPU: Graded-Effect Semantics for Race-Free WebGPU Kernels (Lean 4)

**VerifiedGPU** is a Lean 4 project that formalizes a lightweight, WGSL-like kernel model with **graded effects** and uses a **language quantale** to reason compositionally about **race freedom** and **barrier placement**. The first target demo is a verified **Blelloch-style scan** (exclusive prefix sum) with _optimal_ workgroup barriers, plus a path to **certified WGSL emission**.

- Quantale of languages: `Lang α := Set (Word α)` with concatenation and arbitrary joins
- GPU “phase alphabet”: `Phase` (reads/writes/guards/space)
- **Grades**: words over `Phase` (phase traces) with singleton **denotation** into the quantale
- Per-phase obligations: `WritesDisjointPhase`, `NoRAWIntraPhase`
- Goal: Type-checking ⇒ **DRF** in workgroups; barriers **adequate and minimal**

---

## Table of Contents

1. [Why](#why-this-exists)
2. [Getting started](#getting-started)
3. [Design: phases, grades, quantale](#design-in-90-seconds)
4. [Typing rules](#typing-rules)
   - [Rule reference (inference form)](#rule-reference-inference-form)
   - [Explanations & side-conditions](#explanations--side-conditions)

5. [References](#references)
6. [License](#license)
7. [Appendix: Key definitions](#appendix-key-definitions-as-implemented)

---

## Why this exists

GPU kernels are easy to get subtly wrong (missing barriers, aliasing writes, RAW/WAW hazards). Rather than ad-hoc proofs, we:

- track **who reads/writes what, and when** (per **phase**),
- **split phases** at barriers,
- prove **pairwise disjointness** and **intra-phase RAW safety**,
- lift into a **quantale** of phase traces for compositional laws,
- (soon) emit WGSL matching the proven barrier structure.

---

## Getting started

```bash
# optional: reproducible shell
direnv allow     # or: nix develop  /  devenv shell

# ensure toolchain
elan toolchain install $(cat lean-toolchain)
lake build
```

Repo layout:

```
LanguageQuantale.lean   -- Words & languages; quantale instances
Effects.lean            -- GPU phase alphabet, Grade ops, denotation & safety preds
lakefile.lean           -- Lake config (packages & targets)
lean-toolchain          -- Lean toolchain pin
devenv.nix              -- Nix dev shell (elan, git, node)
```

---

## Design in 90 seconds

- A **Phase** summarizes the _intra-epoch_ memory footprint: `reads`, `writes` (each a list of `Access` with `space`, `base`, `idx : Aff2`, `guard`).
- A **Grade** is a **word of phases** (a phase trace). Barriers append a fresh phase boundary.
- **Denotation** embeds a concrete grade as a singleton **language** `{word}` in the quantale `Lang Phase`.
- The **quantale** gives:
  - monoidal sequencing `⊗` for `;`
  - arbitrary joins `⋁` for branching/families
  - order `≤` for refinement
  - distributivity laws to reason compositionally

- The concurrency rule checks per-phase:
  - `WritesDisjointPhase`: distinct threads never write the same `(space, base, addr)`
  - `NoRAWIntraPhase`: reads don’t alias writes in the _same_ phase

---

## Typing rules

Our typing judgment (to be introduced in `Kernel/Typing.lean`) has the shape

[
\Gamma ;\vdash; s ;\triangleright; g
]

> _Read_: “In environment Γ, statement `s` synthesizes grade `g` (its phase trace).”

Grades compose with `⊙` (sequence), and barriers are explicit phase cuts. Guards (`tid % step = phase`) restrict which threads contribute a given access.

### Rule reference (inference form)

Abbreviations:

- `ε` = empty grade
- `g ⊙ h` = sequential composition of grades
- `B_wg(g)` / `B_st(g)` = append a **workgroup/storage** phase boundary
- `R_s(loc,guard)` / `W_s(loc,guard)` = singleton read/write footprint in space `s ∈ {wg, st}`
- `stamp(g,guard)` = attach `guard` to all accesses in `g`
- `⊔` = finite join of grades (branching)
- `Fold(⊙, ε, {g_i})` = left fold (sequential) of a finite family

**Basic constructs**

```
───────────────────────────────                     (T-Skip)
Γ ⊢ skip ▷ ε

───────────────────────────────                     (T-Let)
Γ ⊢ let x := e ▷ ε
```

**Memory effects**

```
──────────────────────────────────────────────────────── (T-Load-wg)
Γ ⊢ load(loc_wg, x) ▷ R_wg(loc_wg, guard_default)

──────────────────────────────────────────────────────── (T-Load-st)
Γ ⊢ load(loc_st, x) ▷ R_st(loc_st, guard_default)

──────────────────────────────────────────────────────── (T-Store-wg)
Γ ⊢ store(loc_wg, e) ▷ W_wg(loc_wg, guard_default)

──────────────────────────────────────────────────────── (T-Store-st)
Γ ⊢ store(loc_st, e) ▷ W_st(loc_st, guard_default)

───────────────────────────────                         (T-Atomic)
Γ ⊢ atomicAdd(loc, e, x) ▷ ε     [treated race-safe by device semantics]
```

**Composition and barriers**

```
Γ ⊢ s ▷ g     Γ ⊢ t ▷ h
───────────────────────────────                         (T-Seq)
Γ ⊢ s ; t ▷ g ⊙ h

───────────────────────────────                         (T-Barrier-WG)
Γ ⊢ workgroupBarrier ▷ B_wg(ε)

───────────────────────────────                         (T-Barrier-ST)
Γ ⊢ storageBarrier   ▷ B_st(ε)
```

**Guards, branching, families**

```
Γ ⊢ s ▷ g
──────────────────────────────────────────              (T-IfGuard)
Γ ⊢ if (guard) { s } ▷ stamp(g, guard)

{ Γ ⊢ s_i ▷ g_i }_{i∈I finite}
──────────────────────────────────────────              (T-Join-Finite)
Γ ⊢ switch { s_i } ▷ ⊔_{i∈I} g_i

{ Γ ⊢ body(k) ▷ g_k }_{k∈K finite}
──────────────────────────────────────────────────────  (T-ForOffsets)
Γ ⊢ for off∈K { body(off) } ▷ Fold(⊙, ε, { g_k }_{k∈K})
```

**Parallel threads (crux)**

```
Γ ⊢ body ▷ g
Disj_wg(g)   RAWsafe_wg(g)   Disj_st(g)   RAWsafe_st(g)
──────────────────────────────────────────────────────── (T-ForThreads)
Γ ⊢ for_threads { body } ▷ g
```

- `Disj_s(g)`: for every phase of `g` in space `s`, pairwise-disjoint writes across distinct threads
- `RAWsafe_s(g)`: no **intra-phase** read-after-write in space `s` (cross-phase RAW/WAW are OK because barriers split phases)

### Explanations & side-conditions

**(T-Seq)** — _Sequential composition_
The grade of `s ; t` is `g ⊙ h` (concatenation of phase traces).
Denotation law: `⟦g ⊙ h⟧ = ⟦g⟧ ⊗ ⟦h⟧` in the quantale.

**(T-Barrier-WG/ST)** — _Phase splitting_
Introduces a phase boundary for that space; used to separate cross-phase dependences. Operationally: collective barrier; semantically: cut in the word.

**(T-IfGuard)** — _Guard stamping_
All accesses in `g` inherit the guard (`tid % step = phase`). Critical for discharge of disjointness (only **active** threads write).

**(T-Join-Finite)** — _Branching / case split_
Effect is the finite join of branches. Denotation matches set union; distributivity of `⊗` over `⋁` comes from the quantale.

**(T-ForOffsets)** — _Unrolled families / stages_
Sequentially folds a finite family of bodies (`off` values) using `⊙`. In practice, each stage ends with a barrier so phases remain separate.

**(T-ForThreads)** — _Parallel threads / DRF gate_
Keeps the body’s grade `g` but **requires** per-phase, per-space obligations:

- **WritesDisjointPhase**: no two distinct threads write the same `(space, base, addr)` in a phase
- **NoRAWIntraPhase**: no read aliases a write in that same phase
  Cross-phase RAW/WAW are allowed because barriers induce happens-before and move the effects into **different** phases.

> In code, these obligations are proved by arithmetic over `Aff2` indices and guard predicates (e.g. Blelloch upsweep: `tid % (2·off)=0` and writes `buf[tid + 2·off − 1]` are pairwise distinct).

---

## References

- Atkey, **Parameterised Notions of Computation** (graded/parameterised monads)
- Quantales for effect semantics; languages over free monoids
- Blelloch, **Prefix Sums and Their Applications** (work-efficient scans)

---

### Appendix: Key definitions (as implemented)

- `Lang α := Set (Word α)` with `Quantale` instance (concat distributes over `sSup`)
- `Phase` (alphabet): `reads : List Access`, `writes : List Access`
- `Grade := Word Phase`
  `seq : Grade → Grade → Grade`, `barrier : Grade → Grade`, `denote : Grade → Lang Phase`
  Lemmas: `denote_seq`, `denote_unit`
- Obligations:
  `WritesDisjointPhase : Phase → Prop`
  `NoRAWIntraPhase    : Phase → Prop`
