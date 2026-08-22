package c3.kernel.solver.qe

import c3.kernel.solver.cad.*

// ============================================================================
// QE TEST SUITE
// Covers: linear, quadratic, nonlinear, mixed quantifiers, negatives
// ============================================================================

@main def runQETests(): Unit =
  println("C³ Kernel — Quantifier Elimination Tests\n")
  var passed = 0; var failed = 0

  def test(name: String)(block: => Boolean): Unit =
    val result = try block catch case e: Exception => println(s"  EXCEPTION: ${e.getMessage}"); false
    if result then { println(s"  ✓ $name"); passed += 1 }
    else        { println(s"  ✗ $name"); failed += 1 }

  val engine = QEEngine()

  // ── LINEAR ────────────────────────────────────────────────────────────────

  println("LINEAR (Virtual Substitution)")

  // ∃x. x > 0 ∧ x < 1  →  True
  test("∃x. x > 0 ∧ x < 1  →  True") {
    val x = Polynomial.variable(0, 1)
    val f = QFFormula.And(
      QFFormula.Atom(x, Relation.Gt),                                  // x > 0
      QFFormula.Atom(Polynomial.add(x, Polynomial.constant(Rational(-1), 1)), Relation.Lt)  // x - 1 < 0
    )
    val prob = QEProblem(List(Quantifier.Exists("x", 0)), f, Nil, 1)
    val res  = engine.eliminate(prob)
    res.formula == QFFormula.True
  }

  // ∃x. x > a ∧ x < b  →  a < b  (parametric)
  test("∃x. x > a ∧ x < b  →  a < b") {
    val x = Polynomial.variable(0, 3)
    val a = Polynomial.variable(1, 3)
    val b = Polynomial.variable(2, 3)
    val f = QFFormula.And(
      QFFormula.Atom(Polynomial.subtract(x, a), Relation.Gt),
      QFFormula.Atom(Polynomial.subtract(x, b), Relation.Lt)
    )
    val prob = QEProblem(List(Quantifier.Exists("x", 0)), f, List("a", "b"), 3)
    val res  = engine.eliminate(prob)
    // Result should be equivalent to a < b
    val expected = QFFormula.Atom(Polynomial.subtract(a, b), Relation.Lt)
    formulasEquivalent(res.formula, expected, List("a" -> 1, "b" -> 2))
  }

  // ∀x. x² ≥ 0  →  True
  test("∀x. x² ≥ 0  →  True") {
    val x   = Polynomial.variable(0, 1)
    val x2  = Polynomial.multiply(x, x)
    val f   = QFFormula.Atom(x2, Relation.Ge)
    val prob = QEProblem(List(Quantifier.Forall("x", 0)), f, Nil, 1)
    val res  = engine.eliminate(prob)
    res.formula == QFFormula.True
  }

  // ── QUADRATIC ─────────────────────────────────────────────────────────────

  println("\nQUADRATIC")

  // ∃x. x² - 2 = 0  →  True  (√2 exists)
  test("∃x. x² = 2  →  True") {
    val x  = Polynomial.variable(0, 1)
    val x2 = Polynomial.multiply(x, x)
    val p  = Polynomial.add(x2, Polynomial.constant(Rational(-2), 1))
    val f  = QFFormula.Atom(p, Relation.Eq)
    val prob = QEProblem(List(Quantifier.Exists("x", 0)), f, Nil, 1)
    val res  = engine.eliminate(prob)
    res.formula == QFFormula.True
  }

  // ∃x. x² + 1 = 0  →  False  (no real root)
  test("∃x. x² + 1 = 0  →  False") {
    val x  = Polynomial.variable(0, 1)
    val x2 = Polynomial.multiply(x, x)
    val p  = Polynomial.add(x2, Polynomial.constant(Rational(1), 1))
    val f  = QFFormula.Atom(p, Relation.Eq)
    val prob = QEProblem(List(Quantifier.Exists("x", 0)), f, Nil, 1)
    val res  = engine.eliminate(prob)
    res.formula == QFFormula.False
  }

  // ∃x. x² + bx + c = 0  →  b² - 4c ≥ 0  (discriminant condition)
  test("∃x. x² + bx + c = 0  →  b² - 4c ≥ 0") {
    val x = Polynomial.variable(0, 3)
    val b = Polynomial.variable(1, 3)
    val c = Polynomial.variable(2, 3)
    val x2 = Polynomial.multiply(x, x)
    val bx = Polynomial.multiply(b, x)
    val p  = Polynomial.add(Polynomial.add(x2, bx), c)
    val f  = QFFormula.Atom(p, Relation.Eq)
    val prob = QEProblem(List(Quantifier.Exists("x", 0)), f, List("b", "c"), 3)
    val res  = engine.eliminate(prob)
    // b² - 4c ≥ 0
    val b2  = Polynomial.multiply(b, b)
    val c4  = Polynomial.multiplyByScalar(c, Rational(4))
    val disc = Polynomial.subtract(b2, c4)
    val expected = QFFormula.Atom(disc, Relation.Ge)
    formulasEquivalent(res.formula, expected, List("b" -> 2, "c" -> 4))
  }

  // ── MIXED QUANTIFIERS ─────────────────────────────────────────────────────

  println("\nMIXED QUANTIFIERS")

  // ∀x. ∃y. y > x  →  True  (reals are unbounded above)
  test("∀x. ∃y. y > x  →  True") {
    val x = Polynomial.variable(0, 2)
    val y = Polynomial.variable(1, 2)
    val f = QFFormula.Atom(Polynomial.subtract(y, x), Relation.Gt)
    val prob = QEProblem(
      List(Quantifier.Forall("x", 0), Quantifier.Exists("y", 1)),
      f, Nil, 2
    )
    val res = engine.eliminate(prob)
    res.formula == QFFormula.True
  }

  // ∃x. ∀y. x ≤ y  →  False  (no least real)
  test("∃x. ∀y. x ≤ y  →  False") {
    val x = Polynomial.variable(0, 2)
    val y = Polynomial.variable(1, 2)
    val f = QFFormula.Atom(Polynomial.subtract(x, y), Relation.Le)
    val prob = QEProblem(
      List(Quantifier.Exists("x", 0), Quantifier.Forall("y", 1)),
      f, Nil, 2
    )
    val res = engine.eliminate(prob)
    res.formula == QFFormula.False
  }

  // ── NEGATIVE TESTS ────────────────────────────────────────────────────────

  println("\nNEGATIVE TESTS (system must reject / return False)")

  // ∃x ∈ ℝ. x² < 0  →  False
  test("∃x. x² < 0  →  False") {
    val x  = Polynomial.variable(0, 1)
    val x2 = Polynomial.multiply(x, x)
    val f  = QFFormula.Atom(x2, Relation.Lt)
    val prob = QEProblem(List(Quantifier.Exists("x", 0)), f, Nil, 1)
    val res  = engine.eliminate(prob)
    res.formula == QFFormula.False
  }

  // ∀x. x > 0  →  False  (fails for x ≤ 0)
  test("∀x. x > 0  →  False") {
    val x  = Polynomial.variable(0, 1)
    val f  = QFFormula.Atom(x, Relation.Gt)
    val prob = QEProblem(List(Quantifier.Forall("x", 0)), f, Nil, 1)
    val res  = engine.eliminate(prob)
    res.formula == QFFormula.False
  }

  // ── PROOF CERTIFICATES ────────────────────────────────────────────────────

  println("\nPROOF CERTIFICATES")

  test("Certificate extracted for ground problem") {
    val x  = Polynomial.variable(0, 1)
    val x2 = Polynomial.multiply(x, x)
    val p  = Polynomial.add(x2, Polynomial.constant(Rational(-2), 1))
    val f  = QFFormula.Atom(p, Relation.Eq)
    val prob = QEProblem(List(Quantifier.Exists("x", 0)), f, Nil, 1)
    val res  = engine.eliminate(prob)
    val proof = ProofCertificateExtractor.extract(prob, res)
    val check = ProofChecker.check(proof)
    check.valid
  }

  // ── SIMPLIFIER ────────────────────────────────────────────────────────────

  println("\nFORMULA SIMPLIFIER")

  test("¬(A ∧ B) = ¬A ∨ ¬B (De Morgan)") {
    val x = Polynomial.variable(0, 1)
    val a = QFFormula.Atom(x, Relation.Gt)
    val b = QFFormula.Atom(x, Relation.Lt)
    val f = QFFormula.Not(QFFormula.And(a, b))
    val s = FormulaSimplifier.pushNegationInward(f)
    s == QFFormula.Or(QFFormula.Atom(x, Relation.Le), QFFormula.Atom(x, Relation.Ge))
  }

  test("True ∧ F = F") {
    val x = Polynomial.variable(0, 1)
    val f = QFFormula.And(QFFormula.True, QFFormula.Atom(x, Relation.Gt))
    val s = FormulaSimplifier.eliminateTautologies(f)
    s == QFFormula.Atom(x, Relation.Gt)
  }

  test("False ∨ F = F") {
    val x = Polynomial.variable(0, 1)
    val f = QFFormula.Or(QFFormula.False, QFFormula.Atom(x, Relation.Gt))
    val s = FormulaSimplifier.eliminateTautologies(f)
    s == QFFormula.Atom(x, Relation.Gt)
  }

  // ── SUMMARY ───────────────────────────────────────────────────────────────

  println(s"\n$passed passed, $failed failed")
  if failed > 0 then System.exit(1)

// Equivalence check on a finite sample of parameter values
def formulasEquivalent(
  f1: QFFormula, f2: QFFormula,
  varSamples: List[(String, Int)]
): Boolean =
  val testPoints: List[Map[String, Rational]] =
    List(-2, -1, 0, 1, 2, 3).flatMap { v1 =>
      List(-2, -1, 0, 1, 2, 3).map { v2 =>
        varSamples.zip(List(v1, v2)).map { case ((name, _), value) =>
          name -> Rational(value)
        }.toMap
      }
    }
  testPoints.forall { pt =>
    QFFormula.evaluate(f1, pt) == QFFormula.evaluate(f2, pt)
  }
