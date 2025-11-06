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


$$
\Gamma \vdash s \triangleright g
$$

> _Read_: “In environment Γ, statement `s` synthesizes grade `g` (its phase trace).”

Grades compose with `⊙` (sequence), and barriers are explicit phase cuts. Guards (`tid % step = phase`) restrict which threads contribute a given access.

### Rule reference (inference form)

Abbreviations:

- `ε` = empty grade (`Grade.eps`)
- `g ⊙ h` = sequential composition (`Grade.seq g h`)
- `B(g)` = append a phase boundary (`g ⊙ Grade.ofBarrier`)
- `R(loc)` / `W(loc)` = singleton read/write footprints from `loc`
- `stamp(g,guard)` = attach `guard` to all accesses in `g`

**Basic constructs**

```
───────────────────────────────                     (T-Skip)
Γ ⊢ skip ▷ ε

───────────────────────────────                     (T-Let)
Γ ⊢ let x := e ▷ ε
```

**Memory effects**

```
───────────────────────────────────────────          (T-Load)
Γ ⊢ load loc dst ▷ R(loc)

───────────────────────────────────────────          (T-Store)
Γ ⊢ store loc rhs ▷ W(loc)

───────────────────────────────                         (T-Atomic)
Γ ⊢ atomicAdd loc rhs dst ▷ ε     [treated race-safe by device semantics]
```

**Composition and barriers**

```
Γ ⊢ s ▷ g     Γ ⊢ t ▷ h
───────────────────────────────                         (T-Seq)
Γ ⊢ s ; t ▷ g ⊙ h

───────────────────────────────                         (T-Barrier-WG)
Γ ⊢ workgroupBarrier ▷ B(ε)

───────────────────────────────                         (T-Barrier-ST)
Γ ⊢ storageBarrier   ▷ B(ε)
```

**Guards and families**

```
Γ ⊢ s ▷ g
──────────────────────────────────────────              (T-IfGuard)
Γ ⊢ if (guard) { s } ▷ stamp(g, guard)

───────────────────────────────                     (T-ForOffsets-∅)
Γ ⊢ for offsets [] ▷ ε

Γ ⊢ s ▷ g₁    Γ ⊢ for offsets ks ▷ g₂
──────────────────────────────────────────            (T-ForOffsets-Cons)
Γ ⊢ for offsets ((k, s) :: ks) ▷ g₁ ⊙ g₂
```

**Parallel threads (crux)**

```
Γ ⊢ body ▷ g
∀ p ∈ phases(g), WritesDisjointPhase p ∧ NoRAWIntraPhase p
──────────────────────────────────────────────────────── (T-ForThreads)
Γ ⊢ for_threads { body } ▷ g
```

- `phases(g)` is `Grade.phases g` (exposed in Lean for the side-condition)
- `WritesDisjointPhase` / `NoRAWIntraPhase` come from `Effects.lean`

### Explanations & side-conditions

**(T-Load/T-Store)** — _Singleton footprints_
Reads and writes contribute singleton phases (`Grade.ofRead/ofWrite`) guarded by `guardAll`. Memory space is distinguished inside `loc.space`.

**(T-Seq)** — _Sequential composition_
The grade of `s ; t` is `g ⊙ h` (concatenation of phase traces).
Denotation law: `⟦g ⊙ h⟧ = ⟦g⟧ ⊗ ⟦h⟧` in the quantale.

**(T-Barrier-WG/ST)** — _Phase splitting_
Both rules currently share the same barrier phase (`Grade.ofBarrier`); you can refine them later to track workgroup/storage separately.

**(T-IfGuard)** — _Guard stamping_
All accesses in `g` inherit the guard (`tid % step = phase`). Critical for discharge of disjointness (only **active** threads write).

**(T-ForOffsets-∅/Cons)** — _Finite stage sequencing_
`for offsets` is encoded as an explicit list. The empty list contributes `ε`; each cons point sequences the head grade in front of the recursive result, mirroring the Lean constructors `g_for_offsets_nil` / `g_for_offsets_cons`.

**(T-ForThreads)** — _Parallel threads / DRF gate_
Keeps the body’s grade `g` but **requires** the side-condition `(∀ p ∈ Grade.phases g, WritesDisjointPhase p ∧ NoRAWIntraPhase p)`. Cross-phase hazards remain allowed because barriers split the word into distinct phases.

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
