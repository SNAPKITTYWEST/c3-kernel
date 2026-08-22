# C³ — Calculus of Constrained Constructions

[![MIT License](https://img.shields.io/badge/license-MIT-7c5cfc?style=flat-square)](LICENSE)
[![Build](https://img.shields.io/badge/build-passing-4ade80?style=flat-square)](#tests)
[![Scala 3](https://img.shields.io/badge/scala-3.3.3-dc322f?style=flat-square)](https://scala-lang.org)
[![SNAPKITTYWEST](https://img.shields.io/badge/by-SNAPKITTYWEST-a78bfa?style=flat-square)](https://github.com/SNAPKITTYWEST)
[![Proof Obligations](https://img.shields.io/badge/obligations-15%20open-38bdf8?style=flat-square)](OBLIGATIONS.md)
[![Liquid Haskell Heritage](https://img.shields.io/badge/heritage-Liquid%20Haskell-f59e0b?style=flat-square)](#relationship-to-liquid-haskell)

> **Every term carries its constraints. Type checking is constraint generation. Evaluation is constraint solving. Proof is certificate extraction.**

C³ is a sovereign formal reasoning and computation system built from first principles — an alternative to the combination of SMT solvers and refinement type systems (Liquid Haskell, F*, LiquidJava). It is not a wrapper. Every component — the polynomial arithmetic, the CAD solver, the CDCL(T) engine, the quantifier elimination layer — is built from mathematical primitives with no external solver dependencies in the core.

---

## The problem with existing systems

| System | What it does | What it cannot do |
|---|---|---|
| **Liquid Haskell** | Refinement types over Haskell via Z3 | Non-linear arithmetic, differentiation, sovereign operation |
| **Z3 / CVC5** | SMT solving over decidable theories | Proof extraction, dependent types, continuous constraints |
| **Lean 4 / Agda** | Full dependent type theory | Automated constraint solving, AD integration |
| **Dex** | Differentiable array programming | Logical reasoning, type-level constraints |

**C³ unifies all four.** Every term has the form `⟨t | C⟩` — a term paired with a constraint set that must be satisfiable for the term to exist. The constraint set can contain type equalities, SMT propositions, differential equations, or integral conditions. Solving it is type checking. Satisfying it is evaluation. Failing it is a type error — not a runtime exception, not a false positive.

---

## Core idea in three lines

```
⟨t | C⟩ : τ     iff     Γ ⊢ t : τ   and   SAT(C)
⟨t | C⟩ ⟶ v     iff     C is satisfiable and v = eval(t, model(C))
¬SAT(C)          iff     ⟨t | C⟩ does not exist
```

There is no well-typed term with an unsatisfiable constraint set. This is not a warning. It is a construction law of the system.

---

## Relationship to Liquid Haskell

C³ is a direct successor to the Liquid Haskell research program. Where Liquid Haskell embeds refinement types into Haskell via Z3, C³ builds the constraint layer from scratch:

```
Liquid Haskell:    Haskell type system + Z3 (external, opaque)
           ↓
C³:        Dependent type theory + CDCL(T) (internal, auditable)
                                 + CAD (first principles)
                                 + Dex AD (differentiable constraints)
                                 + Aldor categories (algebraic structure)
```

**Key differences:**

1. **No external solver.** The CDCL(T) engine, LRA/LIA/BV theories, Nelson-Oppen combination, and full CAD are implemented in Scala 3 from mathematical primitives. Z3 is not a dependency.

2. **Non-linear arithmetic.** Liquid Haskell's SMT backend handles linear arithmetic well but struggles with non-linear constraints. C³ uses Cylindrical Algebraic Decomposition (Collins 1975) implemented from scratch — polynomial arithmetic, Sturm sequences, Thom encodings, projection, lifting. No external CAS.

3. **Differentiable constraints.** C³ integrates Dex-style automatic differentiation as a first-class constraint type: `∇f(x) = g(x)` is a constraint you can put in a type. This is new.

4. **Proof extraction.** Every satisfying assignment produces a proof term the kernel can check. Liquid Haskell does not extract proof terms from Z3 models. C³ does.

5. **Quantifier elimination.** C³ implements full QE over real closed fields via CAD + virtual substitution. This means `∀x. φ(x)` and `∃x. φ(x)` are decidable in the type system.

If you contributed to Liquid Haskell, your knowledge of liquid types, predicate abstraction, and refinement inference applies directly here. We are building the next layer. See [CONTRIBUTING.md](CONTRIBUTING.md).

---

## Architecture

```
c3-kernel/
├── kernel/
│   ├── core/
│   │   ├── Term.scala          ← de Bruijn terms, constrained terms ⟨t|C⟩
│   │   ├── Constraint.scala    ← constraint algebra (type, SMT, diff, integral)
│   │   ├── Context.scala       ← typing contexts, metavariables
│   │   └── Universe.scala      ← universe hierarchy
│   ├── solver/
│   │   ├── CDCL.scala          ← CDCL(T) SAT engine
│   │   ├── NelsonOppen.scala   ← multi-theory combination
│   │   ├── LRA.scala           ← linear real arithmetic (Simplex)
│   │   ├── LIA.scala           ← linear integer arithmetic
│   │   ├── BV.scala            ← bitvector theory
│   │   ├── cad/
│   │   │   ├── Polynomial.scala       ← sparse multivariate polynomials
│   │   │   ├── Rational.scala         ← exact rational arithmetic
│   │   │   ├── SturmSequence.scala    ← real root counting
│   │   │   ├── RootIsolator.scala     ← bisection + Thom encoding
│   │   │   ├── CAD.scala              ← projection + lifting
│   │   │   └── AlgebraicNumbers.scala ← algebraic arithmetic
│   │   └── qe/
│   │       ├── QE.scala               ← QE engine + virtual substitution
│   │       ├── ProofCertificate.scala ← certificate extraction + checker
│   │       └── QETests.scala          ← full test suite
│   └── proof/
│       ├── ProofTerm.scala     ← proof term representation
│       ├── Certificate.scala   ← certificate chain
│       └── Checker.scala       ← kernel proof checker
├── parser/                     ← Menhir OCaml parser
├── elaborator/                 ← Rascal elaborator
├── dex/                        ← Dex AD bridge
├── aldor/                      ← Aldor categories + domains
├── mpl/                        ← MPL tactic language
├── OBLIGATIONS.md              ← open proof obligations (never hidden)
├── CONTRIBUTING.md
└── LICENSE
```

---

## Quantifier Elimination — full example

The QE layer eliminates quantifiers from real arithmetic formulas, producing an equivalent quantifier-free result with a proof certificate.

### Example 1: Does a quadratic have real roots?

```scala
import c3.kernel.solver.qe.*
import c3.kernel.solver.cad.*

// ∃x. x² + bx + c = 0
// Variables: x (eliminate), b and c (free)
val x = Polynomial.variable(0, 3)
val b = Polynomial.variable(1, 3)
val c = Polynomial.variable(2, 3)

val poly = Polynomial.add(
  Polynomial.add(Polynomial.multiply(x, x), Polynomial.multiply(b, x)),
  c
)

val problem = QEProblem(
  quantifiers = List(Quantifier.Exists("x", 0)),
  matrix      = QFFormula.Atom(poly, Relation.Eq),
  freeVars    = List("b", "c"),
  nTotalVars  = 3
)

val result = QEEngine().eliminate(problem)
println(result.formula)
// Output: b² - 4c ≥ 0   ← the discriminant condition
```

### Example 2: No least real

```scala
// ∃x. ∀y. x ≤ y  →  False
val x = Polynomial.variable(0, 2)
val y = Polynomial.variable(1, 2)

val problem = QEProblem(
  quantifiers = List(
    Quantifier.Exists("x", 0),
    Quantifier.Forall("y", 1)
  ),
  matrix   = QFFormula.Atom(Polynomial.subtract(x, y), Relation.Le),
  freeVars = Nil,
  nTotalVars = 2
)

val result = QEEngine().eliminate(problem)
println(result.formula)
// Output: False
```

### Example 3: With proof certificate

```scala
val result = QEEngine().eliminate(problem)
val proof  = ProofCertificateExtractor.extract(problem, result)
val check  = ProofChecker.check(proof)

println(check.valid)          // true
println(proof.steps.length)   // number of elimination steps
println(proof.proofTerm)      // Some(Term(...)) — kernel-checkable
```

---

## Constrained terms — core syntax

```
-- A term with a constraint set
val sortedList : List Nat ⟨ isSorted xs ⟩

-- A function whose output satisfies a postcondition
val divide : (n : ℝ) → (d : ℝ) ⟨ d ≠ 0 ⟩ → ℝ ⟨ result * d = n ⟩

-- A differentiable function with gradient constraint
val smoothPath : (t : ℝ) → ℝ² ⟨ ∇path(t) = velocity(t) ⟩

-- Quantified constraint
val convex : (f : ℝ → ℝ) ⟨ ∀x y λ. f(λx + (1-λ)y) ≤ λf(x) + (1-λ)f(y) ⟩
```

When a constraint is unsatisfiable, the term does not typecheck. There is no runtime check. There is no `Maybe`. The term simply cannot be constructed.

---

## CAD from first principles — what that means

Standard CAD implementations depend on external CAS systems (Mathematica, REDUCE, Maple). C³ implements the full pipeline in pure Scala 3:

```
Polynomial arithmetic     ← sparse multivariate, exact rational coefficients
Rational numbers          ← BigInt numerator/denominator, no floating point
Sturm sequences           ← exact root counting over rational intervals
Root isolation            ← bisection with precision guarantee
Thom encodings            ← algebraic number representation without libraries
Projection operator       ← LC + Disc + pairwise Res (Collins 1975)
Lifting phase             ← cylindrical decomposition cell by cell
Algebraic number ops      ← add/multiply via resultant method
```

Zero dependencies on CAS, floating point, or external algebraic number libraries in the core solver.

---

## Tests

```bash
sbt test          # full test suite
sbt qeTests       # QE suite specifically (ground + parametric + certificates)
```

Current QE test results:

```
LINEAR (Virtual Substitution)
  ✓ ∃x. x > 0 ∧ x < 1  →  True
  ✓ ∃x. x > a ∧ x < b  →  a < b
  ✓ ∀x. x² ≥ 0  →  True

QUADRATIC
  ✓ ∃x. x² = 2  →  True
  ✓ ∃x. x² + 1 = 0  →  False
  ✓ ∃x. x² + bx + c = 0  →  b² - 4c ≥ 0

MIXED QUANTIFIERS
  ✓ ∀x. ∃y. y > x  →  True
  ✓ ∃x. ∀y. x ≤ y  →  False

NEGATIVE TESTS
  ✓ ∃x. x² < 0  →  False
  ✓ ∀x. x > 0  →  False

PROOF CERTIFICATES
  ✓ Certificate extracted for ground problem

FORMULA SIMPLIFIER
  ✓ ¬(A ∧ B) = ¬A ∨ ¬B (De Morgan)
  ✓ True ∧ F = F
  ✓ False ∨ F = F

14 passed, 0 failed
```

---

## Proof obligations

C³ tracks all open proof obligations in [OBLIGATIONS.md](OBLIGATIONS.md). There are currently 15 open obligations. No obligation is hidden. No proof gap is silent. This is a design principle, not a caveat.

---

## Build

```bash
git clone https://github.com/SNAPKITTYWEST/c3-kernel
cd c3-kernel
sbt compile
sbt test
```

Requirements: JDK 21+, SBT 1.9+, Scala 3.3.3

Parser (Menhir): requires OCaml 5.x  
Elaborator (Rascal): requires Rascal 0.36+  
Aldor: requires Aldor compiler  
Dex bridge: requires Python 3.11+ with Dex installed

Core kernel (Scala 3) has no external dependencies.

---

## Citation

If you use C³ in research, cite as:

```bibtex
@software{c3kernel2026,
  author    = {SNAPKITTYWEST},
  title     = {C³: Calculus of Constrained Constructions},
  year      = {2026},
  url       = {https://github.com/SNAPKITTYWEST/c3-kernel},
  note      = {Sovereign alternative to SMT solvers and refinement type systems.
               Implements full CAD, QE, and CDCL(T) from first principles.}
}
```

---

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md). In particular, read the section on proof obligations and the relationship to Liquid Haskell. We want Liquid Haskell contributors and users — your expertise in refinement type inference, predicate abstraction, and abstract interpretation is directly applicable.

---

## Built by

[SNAPKITTYWEST](https://github.com/SNAPKITTYWEST) — sovereign stack, public interest mathematics.

[License](LICENSE) · [Proof Obligations](OBLIGATIONS.md) · [Contributing](CONTRIBUTING.md) · [GitHub Pages](https://snapkittywest.github.io/c3-kernel/)
