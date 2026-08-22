# Proof Obligations

Open proof obligations in the C³ kernel. Every `TODO` in the codebase has a corresponding entry here. This is the mathematical debt register.

---

## [OBL-001] Soundness of C³ Typing

**Statement**: If `Γ ⊢ ⟨t|C⟩ : τ` and `SAT(C)` then `t` inhabits `τ` in the underlying dependent type theory.

**Status**: TODO
**Method**: Logical relations over the constraint-extended term model
**Blocking**: Kernel release

---

## [OBL-002] Completeness in Decidable Fragment

**Statement**: If `∃t. Γ ⊢ t : τ` in the decidable fragment (LRA + LIA + BV), the C³ solver finds a witness.

**Status**: TODO
**Method**: Model construction from CDCL(T) satisfying assignment
**Blocking**: OBL-001

---

## [OBL-003] Constraint Preservation under Evaluation

**Statement**: `eval(⟨t|C⟩) = ⟨v|∅⟩` implies `SAT(C)`.

**Status**: TODO
**Method**: Progress + Preservation lemmas on the constrained reduction relation
**Blocking**: Evaluator correctness

---

## [OBL-004] CAD Projection Correctness

**Statement**: The projection set `Project(P, xₙ)` is sign-invariant for `P` over every cell produced by the lifting phase.

**Status**: TODO
**Method**: Collins' theorem (1975) + subresultant PRS theory
**Blocking**: QE soundness

---

## [OBL-005] CAD Lifting Completeness

**Statement**: The union of all cells in `Lift(S, P)` covers `ℝⁿ`.

**Status**: TODO
**Method**: Induction on dimension + real root completeness of Sturm sequences
**Blocking**: OBL-004

---

## [OBL-006] Thom Encoding Uniqueness

**Statement**: For any polynomial `f ∈ ℚ[x]` and any two distinct real roots `α ≠ β`, their Thom encodings are distinct.

**Status**: TODO
**Method**: Rolle's theorem + sign variation argument
**Blocking**: Algebraic number comparison correctness

---

## [OBL-007] Sturm Sequence Root Count

**Statement**: `signChangesAt(lo) - signChangesAt(hi)` equals the number of distinct real roots of `f` in `(lo, hi)`.

**Status**: TODO
**Method**: Sturm's theorem (classical)
**Blocking**: Root isolation correctness

---

## [OBL-008] Virtual Substitution Equivalence (Linear)

**Statement**: `∃x. φ(x)` is equivalent to `φ(-∞) ∨ ⋁ᵢ φ(tᵢ)` where `tᵢ` are the boundary terms of `φ`.

**Status**: TODO
**Method**: Weispfenning (1988) virtual substitution theorem for linear arithmetic
**Blocking**: VS soundness

---

## [OBL-009] Virtual Substitution Equivalence (Quadratic)

**Statement**: VS elimination is sound for formulas with polynomials of degree ≤ 2.

**Status**: TODO
**Method**: Loos-Weispfenning (1993) quadratic VS theorem
**Blocking**: OBL-008

---

## [OBL-010] Nelson-Oppen Combination Soundness

**Statement**: If each theory `Tᵢ` is stably infinite and the combined constraint set is `T₁ ∪ T₂`-unsatisfiable, Nelson-Oppen detects this.

**Status**: TODO
**Method**: Nelson-Oppen (1979) combination theorem
**Blocking**: Multi-theory constraint solving

---

## [OBL-011] LRA Simplex Soundness

**Statement**: If the Simplex tableau reports `UNSAT`, the linear arithmetic formula is unsatisfiable over ℚ.

**Status**: TODO
**Method**: Farkas' lemma + LP duality
**Blocking**: LRA theory solver

---

## [OBL-012] CDCL Termination

**Statement**: The CDCL(T) loop terminates on any finite constraint set.

**Status**: TODO
**Method**: Well-founded measure on (clause database size, unassigned variables)
**Blocking**: Solver correctness

---

## [OBL-013] Dex AD Correctness

**Statement**: `diff(f) = g` implies `∀x. ∇f(x) = g(x)` in the standard real analysis sense.

**Status**: TODO
**Method**: Dex AD correctness (external — cite Dex paper)
**Blocking**: Differential constraint correctness

---

## [OBL-014] QE Completeness

**Statement**: For every sentence `φ` in the language of real closed fields, the QE engine produces an equivalent quantifier-free sentence.

**Status**: TODO
**Method**: Tarski (1951) decidability of RCF + completeness of CAD (Collins 1975)
**Blocking**: OBL-004, OBL-005

---

## [OBL-015] Proof Certificate Soundness

**Statement**: If `ProofChecker.check(proof)` returns `valid = true`, then `proof.result` is logically equivalent to `proof.problem.matrix` (with quantifiers instantiated as specified).

**Status**: TODO
**Method**: Induction on proof structure
**Blocking**: Kernel trust

---

## Summary

| ID | Area | Status | Blocking |
|---|---|---|---|
| OBL-001 | Kernel soundness | TODO | Release |
| OBL-002 | Kernel completeness | TODO | OBL-001 |
| OBL-003 | Evaluator | TODO | Evaluator |
| OBL-004 | CAD projection | TODO | QE |
| OBL-005 | CAD lifting | TODO | OBL-004 |
| OBL-006 | Thom encoding | TODO | Alg. numbers |
| OBL-007 | Sturm sequences | TODO | Root isolation |
| OBL-008 | VS linear | TODO | VS |
| OBL-009 | VS quadratic | TODO | OBL-008 |
| OBL-010 | Nelson-Oppen | TODO | Multi-theory |
| OBL-011 | LRA Simplex | TODO | LRA |
| OBL-012 | CDCL termination | TODO | Solver |
| OBL-013 | Dex AD | TODO | Diff constraints |
| OBL-014 | QE completeness | TODO | OBL-004/005 |
| OBL-015 | Certificate soundness | TODO | Kernel |

15 open obligations. No obligation is hidden. No proof gap is silent.
