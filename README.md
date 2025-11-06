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

$$
\frac{\ }{\Gamma \vdash \texttt{skip} \triangleright \varepsilon}\quad(\textsc{T-Skip})
$$

$$
\frac{\ }{\Gamma \vdash \texttt{let}\ x:=e \triangleright \varepsilon}\quad(\textsc{T-Let})
$$

**Memory effects**

$$
\frac{\ }{\Gamma \vdash \texttt{load}\;loc\;dst \triangleright R(loc)}\quad(\textsc{T-Load})
$$

$$
\frac{\ }{\Gamma \vdash \texttt{store}\;loc\;rhs \triangleright W(loc)}\quad(\textsc{T-Store})
$$

$$
\frac{\ }{\Gamma \vdash \texttt{atomicAdd}\;loc\;rhs\;dst \triangleright \varepsilon}\quad(\textsc{T-Atomic})
$$

**Composition and barriers**

$$
\frac{\Gamma \vdash s \triangleright g \quad \Gamma \vdash t \triangleright h}{\Gamma \vdash s ; t \triangleright g \odot h}\quad(\textsc{T-Seq})
$$

$$
\frac{\ }{\Gamma \vdash \texttt{workgroupBarrier} \triangleright B(\varepsilon)}\quad(\textsc{T-Barrier-WG})
$$

$$
\frac{\ }{\Gamma \vdash \texttt{storageBarrier} \triangleright B(\varepsilon)}\quad(\textsc{T-Barrier-ST})
$$

**Guards and families**

$$
\frac{\Gamma \vdash s \triangleright g}{\Gamma \vdash \texttt{if}\ (guard)\ \{s\} \triangleright stamp(g,\,guard)}\quad(\textsc{T-IfGuard})
$$

$$
\frac{\ }{\Gamma \vdash \texttt{for\_offsets}\;[] \triangleright \varepsilon}\quad(\textsc{T-ForOffsets-}\varnothing)
$$

$$
\frac{\Gamma \vdash s \triangleright g_1 \quad \Gamma \vdash \texttt{for\_offsets}\;ks \triangleright g_2}{\Gamma \vdash \texttt{for\_offsets}\;((k,s)::ks) \triangleright g_1 \odot g_2}\quad(\textsc{T-ForOffsets-Cons})
$$

**Parallel threads (crux)**

$$
\frac{\Gamma \vdash body \triangleright g \quad \forall p \in \mathrm{phases}(g),\;\mathrm{WritesDisjointPhase}(p) \wedge \mathrm{NoRAWIntraPhase}(p)}{\Gamma \vdash \texttt{for\_threads}\ \{body\} \triangleright g}\quad(\textsc{T-ForThreads})
$$

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
