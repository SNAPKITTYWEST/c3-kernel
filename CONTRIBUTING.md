# Contributing to C³

C³ (Calculus of Constrained Constructions) is a live research system. Contributions are welcome at every level — from fixing a typo in a proof obligation to implementing a new theory solver. Read this document before opening a PR.

---

## What we are building

C³ is a sovereign alternative to SMT solvers and refinement type systems (Liquid Haskell, F*, LiquidJava). The core insight: every term carries a constraint set. Type checking *is* constraint generation. Evaluation *is* constraint solving. Proof *is* certificate extraction.

We take institutional rigor seriously. Every claim in this codebase should be either:
- Proved (with a proof term the kernel can check), or
- Explicitly marked `TODO` with a proof obligation entry in `OBLIGATIONS.md`

We do not ship unacknowledged holes.

---

## Contribution areas

### Theory
- New SMT theory solvers (strings, floating point, sets)
- Completeness/soundness proofs for existing theories
- CAD optimizations (NLSAT, MCSAT alternatives)
- Proof term generation for theory lemmas

### Kernel
- Type checker improvements
- Universe polymorphism
- Cumulative vs non-cumulative universes
- Definitional equality algorithms (NBE, higher-order unification)

### QE Layer
- Extending virtual substitution to higher degrees
- Partial CAD (PCAD) for faster elimination
- QEPCAD integration
- Benchmark suite against Mathematica/Maple/Redlog

### Language
- Menhir parser extensions
- Rascal elaborator improvements
- MPL tactic language
- Aldor category contributions

### Infrastructure
- Benchmarks against Z3, CVC5, Yices
- Property-based testing (ScalaCheck)
- Dex bridge improvements

---

## Standards

### Proof obligations

Every `TODO` proof obligation must have a corresponding entry in `OBLIGATIONS.md`:

```
## [OBL-042] Soundness of CAD Projection

**Statement**: If `Project(P, xₙ)` is satisfied at a sample point,
then the sign conditions of `P` are invariant in the corresponding cell.

**Status**: TODO
**Method**: Collins' theorem + subresultant theory
**Blocking**: QE completeness
```

### Code style

- Scala 3: use `enum`, `opaque type`, extension methods
- No `null`. No `var` unless inside a local solver loop with documented justification
- Every public method has a one-line contract comment
- No silent failures: return `Either` or a typed error, never throw in kernel code

### Commits

Follow Conventional Commits:

```
feat(qe): add virtual substitution for quadratic case
fix(cad): correct Thom encoding for negative leading coefficient
proof(lra): soundness of Simplex phase 1 via Farkas lemma
test(qe): add discriminant condition benchmark
docs(contributing): clarify proof obligation format
```

### Pull requests

1. Every PR must pass all existing tests (`sbt test`)
2. New features require new tests
3. New proof obligations require `OBLIGATIONS.md` entries
4. Breaking changes to the kernel require an RFC filed as an issue first

---

## Relationship to Liquid Haskell

C³ is a successor project. Where Liquid Haskell embeds refinement types into Haskell's type system via SMT-backed liquid types, C³ builds the constraint system from first principles:

| | Liquid Haskell | C³ |
|---|---|---|
| **Base language** | Haskell + GHC | C³ kernel (independent) |
| **Constraint backend** | Z3 (external) | CDCL(T) built from scratch |
| **Differentiation** | None | Dex AD integration |
| **Nonlinear arithmetic** | Limited | Full CAD from first principles |
| **Proof extraction** | No | Yes — C³ proof terms |
| **Sovereignty** | Depends on GHC/Z3 | Zero external dependencies in core |

If you are a Liquid Haskell contributor or user, your knowledge of refinement type theory, predicate abstraction, and abstract interpretation applies directly here. We want that expertise in this project.

---

## Getting started

```bash
git clone https://github.com/SNAPKITTYWEST/c3-kernel
cd c3-kernel
sbt test          # run all tests
sbt run           # launch REPL
sbt qeTests       # QE test suite specifically
```

Open an issue with the label `good-first-issue` to find an entry point.

---

## Code of conduct

Be direct. Be precise. Show your work. Disagreement about proofs and algorithms is expected and healthy. Personal attacks are not tolerated.

---

## Contact

Open an issue. We respond.
