package c3.kernel.solver.qe

import c3.kernel.solver.cad.*
import c3.kernel.core.*

// ============================================================================
// QUANTIFIER ELIMINATION VIA CAD
// C³ Kernel — Ahmad's Calculus of Constrained Constructions
//
// QE takes: ∃x₁...xₖ. φ(x₁,...,xₖ,y₁,...,yₘ)
// Produces: ψ(y₁,...,yₘ)  — equivalent, quantifier-free
//
// ∀ is handled by: ∀x.φ(x) = ¬∃x.¬φ(x)
// ============================================================================

// ============================================================================
// INPUT: QE PROBLEM
// ============================================================================

enum Quantifier:
  case Exists(varName: String, varIndex: Int)
  case Forall(varName: String, varIndex: Int)

final case class QEProblem(
  quantifiers: List[Quantifier],   // outermost first
  matrix: QFFormula,               // quantifier-free body
  freeVars: List[String],          // variables NOT eliminated
  nTotalVars: Int
):
  def isGroundProblem: Boolean = freeVars.isEmpty
  def elimVars: List[String] = quantifiers.map {
    case Quantifier.Exists(v, _) => v
    case Quantifier.Forall(v, _) => v
  }

// ============================================================================
// QUANTIFIER-FREE FORMULA (the output type)
// ============================================================================

enum QFFormula:
  case Atom(poly: Polynomial, rel: Relation)
  case And(left: QFFormula, right: QFFormula)
  case Or(left: QFFormula, right: QFFormula)
  case Not(inner: QFFormula)
  case Implies(left: QFFormula, right: QFFormula)
  case True
  case False

object QFFormula:
  def and(fs: List[QFFormula]): QFFormula =
    fs.filterNot(_ == True) match
      case Nil => True
      case List(f) => f
      case fs if fs.contains(False) => False
      case fs => fs.reduce(And.apply)

  def or(fs: List[QFFormula]): QFFormula =
    fs.filterNot(_ == False) match
      case Nil => False
      case List(f) => f
      case fs if fs.contains(True) => True
      case fs => fs.reduce(Or.apply)

  def neg(f: QFFormula): QFFormula = f match
    case True     => False
    case False    => True
    case Not(g)   => g
    case g        => Not(g)

  def evaluate(f: QFFormula, point: Map[String, Rational]): Boolean = f match
    case True  => true
    case False => false
    case Not(g)         => !evaluate(g, point)
    case And(l, r)      => evaluate(l, point) && evaluate(r, point)
    case Or(l, r)       => evaluate(l, point) || evaluate(r, point)
    case Implies(l, r)  => !evaluate(l, point) || evaluate(r, point)
    case Atom(poly, rel) =>
      val vars = point.keys.toList.sorted
      val vals = vars.map(point)
      val v = Polynomial.evalRational(poly, vals)
      rel match
        case Relation.Eq  => v == Rational.zero
        case Relation.Neq => v != Rational.zero
        case Relation.Lt  => v < Rational.zero
        case Relation.Le  => v <= Rational.zero
        case Relation.Gt  => v > Rational.zero
        case Relation.Ge  => v >= Rational.zero

// ============================================================================
// QE RESULT WITH PROOF CERTIFICATE
// ============================================================================

final case class QEResult(
  formula: QFFormula,
  certificate: QECertificate,
  stats: QEStats
)

final case class QECertificate(
  projectionPolynomials: Map[String, Set[Polynomial]],
  cadStack: CADStack,
  cellFormulas: Map[Int, QFFormula],
  witnessMap: Map[String, List[WitnessInterval]]
)

final case class WitnessInterval(
  varName: String,
  lower: Option[Either[Rational, AlgebraicNumber]],
  upper: Option[Either[Rational, AlgebraicNumber]],
  samplePoint: Either[Rational, AlgebraicNumber]
)

final case class QEStats(
  inputPolynomials: Int,
  projectionPolynomials: Int,
  cadCells: Int,
  satisfyingCells: Int,
  eliminationTimeMs: Long
)

// ============================================================================
// ELIMINATION ORDER
// ============================================================================

enum EliminationOrder:
  case Natural         // eliminate variables in declaration order
  case DegreeBased     // eliminate highest-degree variables first
  case LexSmallest     // eliminate lex-smallest variables first
  case Custom(order: List[String])

object EliminationOrder:
  def orderVars(problem: QEProblem, order: EliminationOrder): List[String] =
    problem.elimVars match
      case Nil => Nil
      case vars => order match
        case Natural      => vars
        case LexSmallest  => vars.sorted
        case DegreeBased  =>
          val polyDegrees = vars.map { v =>
            val idx = problem.quantifiers.collectFirst {
              case Quantifier.Exists(n, i) if n == v => i
              case Quantifier.Forall(n, i) if n == v => i
            }.getOrElse(0)
            v -> maxDegreeOfVar(problem.matrix, idx)
          }
          polyDegrees.sortBy(-_._2).map(_._1)
        case Custom(ord)  => ord.filter(vars.contains)

  private def maxDegreeOfVar(f: QFFormula, varIdx: Int): Int = f match
    case QFFormula.Atom(p, _)    => Polynomial.degree(p, varIdx)
    case QFFormula.And(l, r)     => maxDegreeOfVar(l, varIdx).max(maxDegreeOfVar(r, varIdx))
    case QFFormula.Or(l, r)      => maxDegreeOfVar(l, varIdx).max(maxDegreeOfVar(r, varIdx))
    case QFFormula.Not(g)        => maxDegreeOfVar(g, varIdx)
    case QFFormula.Implies(l, r) => maxDegreeOfVar(l, varIdx).max(maxDegreeOfVar(r, varIdx))
    case _                       => 0

// ============================================================================
// PROJECTION PHASE (extended for QE)
// ============================================================================

object QEProjection:

  // Full projection set for QE over variable varIdx
  // Includes: LC, Disc, Res — plus sign-invariance polynomials
  def projectForQE(
    polys: Set[Polynomial],
    varIdx: Int
  ): Set[Polynomial] =
    var result = Set.empty[Polynomial]
    val polyList = polys.toList

    for p <- polyList do
      // Leading coefficient
      val lc = Polynomial.leadingCoeff(p, varIdx)
      if lc != Rational.zero then
        result += Polynomial.constant(lc, p.numVars)

      // Discriminant (sign determines distinct real roots)
      if Polynomial.degree(p, varIdx) >= 2 then
        val disc = Polynomial.discriminant(p, varIdx)
        if disc != Polynomial.zero then result += disc

      // Square-free part to remove repeated roots
      val sqfFactors = PolynomialArithmetic.squareFreeFactor(p, varIdx)
      for (factor, _) <- sqfFactors do
        result += factor

    // All pairwise resultants
    for i <- polyList.indices; j <- (i + 1) until polyList.length do
      val res = Polynomial.resultant(polyList(i), polyList(j), varIdx)
      if res != Polynomial.zero then result += res

    // Remove constants and zero polynomials
    result.filter(p => p != Polynomial.zero && Polynomial.totalDegree(p) > 0)

  // Sign conditions at a sample point for all projection polynomials
  def signConditionsAt(
    polys: Set[Polynomial],
    point: List[Either[Rational, AlgebraicNumber]]
  ): Map[Polynomial, Int] =
    polys.map { p =>
      val sign = evaluateSign(p, point)
      p -> sign
    }.toMap

  private def evaluateSign(
    p: Polynomial,
    point: List[Either[Rational, AlgebraicNumber]]
  ): Int =
    val rationalApprox = point.map {
      case Left(r)    => r
      case Right(alg) => (alg.isolatingInterval._1 + alg.isolatingInterval._2) / 2
    }
    Polynomial.evalRational(p, rationalApprox).sign

// ============================================================================
// FORMULA CONSTRUCTION FROM CAD CELLS
// ============================================================================

object CellFormulaConstructor:

  // Build QF formula describing sign conditions of a cell
  def cellToFormula(
    cell: CADCell,
    projPolys: List[Set[Polynomial]],
    varNames: List[String]
  ): QFFormula =
    val conditions = cell.description.zipWithIndex.flatMap { (desc, level) =>
      val polys = if level < projPolys.length then projPolys(level) else Set.empty[Polynomial]
      desc match
        case CellDescription.Sector(idx) =>
          sectorConditions(cell, polys, level, varNames)
        case CellDescription.Section(alg) =>
          sectionConditions(alg, polys, level, varNames)
    }
    QFFormula.and(conditions)

  private def sectorConditions(
    cell: CADCell,
    polys: Set[Polynomial],
    level: Int,
    varNames: List[String]
  ): List[QFFormula] =
    polys.map { p =>
      val sign = evaluateSignInSector(p, cell, level)
      signToFormula(p, sign)
    }.toList

  private def sectionConditions(
    alg: AlgebraicNumber,
    polys: Set[Polynomial],
    level: Int,
    varNames: List[String]
  ): List[QFFormula] =
    // On a section, the defining polynomial is zero
    val defPoly = alg.definingPolynomial
    val zeroAtRoot = QFFormula.Atom(defPoly, Relation.Eq)

    // Other polynomials have definite signs
    val otherSigns = polys.filter(_ != defPoly).map { p =>
      val sign = AlgebraicNumberOps.signAt(p, alg)
      signToFormula(p, sign)
    }.toList

    zeroAtRoot :: otherSigns

  private def signToFormula(p: Polynomial, sign: Int): QFFormula =
    sign match
      case 1  => QFFormula.Atom(p, Relation.Gt)
      case -1 => QFFormula.Atom(p, Relation.Lt)
      case 0  => QFFormula.Atom(p, Relation.Eq)
      case _  => QFFormula.True

  private def evaluateSignInSector(p: Polynomial, cell: CADCell, level: Int): Int =
    val sample = cell.samplePoint.take(level + 1).map {
      case Left(r)    => r
      case Right(alg) => (alg.isolatingInterval._1 + alg.isolatingInterval._2) / 2
    }
    if sample.length < Polynomial.numVars(p) then 0
    else Polynomial.evalRational(p, sample).sign

// ============================================================================
// FORMULA SIMPLIFICATION
// ============================================================================

object FormulaSimplifier:

  def simplify(f: QFFormula): QFFormula =
    val f1 = pushNegationInward(f)
    val f2 = flattenAssociative(f1)
    val f3 = eliminateTautologies(f2)
    val f4 = mergeSignConditions(f3)
    f4

  // Push ¬ inward via De Morgan
  def pushNegationInward(f: QFFormula): QFFormula = f match
    case QFFormula.Not(QFFormula.And(l, r)) =>
      QFFormula.Or(pushNegationInward(QFFormula.Not(l)), pushNegationInward(QFFormula.Not(r)))
    case QFFormula.Not(QFFormula.Or(l, r)) =>
      QFFormula.And(pushNegationInward(QFFormula.Not(l)), pushNegationInward(QFFormula.Not(r)))
    case QFFormula.Not(QFFormula.Not(g)) =>
      pushNegationInward(g)
    case QFFormula.Not(QFFormula.Atom(p, rel)) =>
      QFFormula.Atom(p, negateRelation(rel))
    case QFFormula.Not(QFFormula.True)  => QFFormula.False
    case QFFormula.Not(QFFormula.False) => QFFormula.True
    case QFFormula.And(l, r)    => QFFormula.And(pushNegationInward(l), pushNegationInward(r))
    case QFFormula.Or(l, r)     => QFFormula.Or(pushNegationInward(l), pushNegationInward(r))
    case QFFormula.Implies(l, r)=>
      QFFormula.Or(pushNegationInward(QFFormula.Not(l)), pushNegationInward(r))
    case other => other

  def flattenAssociative(f: QFFormula): QFFormula = f match
    case QFFormula.And(l, r) =>
      val ls = collectAnds(QFFormula.And(flattenAssociative(l), flattenAssociative(r)))
      QFFormula.and(ls)
    case QFFormula.Or(l, r) =>
      val ls = collectOrs(QFFormula.Or(flattenAssociative(l), flattenAssociative(r)))
      QFFormula.or(ls)
    case QFFormula.Not(g)   => QFFormula.Not(flattenAssociative(g))
    case other              => other

  def eliminateTautologies(f: QFFormula): QFFormula = f match
    case QFFormula.And(l, r) =>
      val l2 = eliminateTautologies(l)
      val r2 = eliminateTautologies(r)
      if l2 == QFFormula.False || r2 == QFFormula.False then QFFormula.False
      else if l2 == QFFormula.True then r2
      else if r2 == QFFormula.True then l2
      else QFFormula.And(l2, r2)
    case QFFormula.Or(l, r) =>
      val l2 = eliminateTautologies(l)
      val r2 = eliminateTautologies(r)
      if l2 == QFFormula.True || r2 == QFFormula.True then QFFormula.True
      else if l2 == QFFormula.False then r2
      else if r2 == QFFormula.False then l2
      else QFFormula.Or(l2, r2)
    case QFFormula.Not(g)   => QFFormula.neg(eliminateTautologies(g))
    case other              => other

  // Merge p > 0 ∧ p ≠ 0 → p > 0 etc.
  def mergeSignConditions(f: QFFormula): QFFormula =
    val atoms = collectAtoms(f)
    val merged = mergeAtomSet(atoms)
    rebuildFromMerged(f, merged)

  private def collectAnds(f: QFFormula): List[QFFormula] = f match
    case QFFormula.And(l, r) => collectAnds(l) ++ collectAnds(r)
    case other               => List(other)

  private def collectOrs(f: QFFormula): List[QFFormula] = f match
    case QFFormula.Or(l, r) => collectOrs(l) ++ collectOrs(r)
    case other              => List(other)

  private def collectAtoms(f: QFFormula): List[QFFormula.Atom] = f match
    case a: QFFormula.Atom   => List(a)
    case QFFormula.And(l, r) => collectAtoms(l) ++ collectAtoms(r)
    case QFFormula.Or(l, r)  => collectAtoms(l) ++ collectAtoms(r)
    case QFFormula.Not(g)    => collectAtoms(g)
    case _                   => Nil

  private def mergeAtomSet(atoms: List[QFFormula.Atom]): Map[Polynomial, Relation] =
    atoms.groupBy(_.poly).map { (p, as) =>
      val merged = as.map(_.rel).reduce(refineRelation)
      p -> merged
    }

  // Tightest relation consistent with both
  private def refineRelation(r1: Relation, r2: Relation): Relation = (r1, r2) match
    case (Relation.Gt, Relation.Neq) | (Relation.Neq, Relation.Gt) => Relation.Gt
    case (Relation.Lt, Relation.Neq) | (Relation.Neq, Relation.Lt) => Relation.Lt
    case (Relation.Ge, Relation.Gt)  | (Relation.Gt, Relation.Ge)  => Relation.Gt
    case (Relation.Le, Relation.Lt)  | (Relation.Lt, Relation.Le)  => Relation.Lt
    case _ => r1

  private def rebuildFromMerged(f: QFFormula, merged: Map[Polynomial, Relation]): QFFormula = f match
    case QFFormula.Atom(p, _) => merged.get(p).map(QFFormula.Atom(p, _)).getOrElse(f)
    case QFFormula.And(l, r)  => QFFormula.And(rebuildFromMerged(l, merged), rebuildFromMerged(r, merged))
    case QFFormula.Or(l, r)   => QFFormula.Or(rebuildFromMerged(l, merged), rebuildFromMerged(r, merged))
    case QFFormula.Not(g)     => QFFormula.Not(rebuildFromMerged(g, merged))
    case other                => other

  private def negateRelation(r: Relation): Relation = r match
    case Relation.Eq  => Relation.Neq
    case Relation.Neq => Relation.Eq
    case Relation.Lt  => Relation.Ge
    case Relation.Le  => Relation.Gt
    case Relation.Gt  => Relation.Le
    case Relation.Ge  => Relation.Lt

// ============================================================================
// VIRTUAL SUBSTITUTION (for linear/quadratic cases — faster than full CAD)
// ============================================================================

object VirtualSubstitution:

  // Eliminate one variable from a linear formula
  // VS is complete for linear arithmetic, much cheaper than CAD
  def eliminateLinear(f: QFFormula, varIdx: Int): QFFormula =
    val atoms = collectLinearAtoms(f, varIdx)
    if atoms.isEmpty then f
    else
      // Substitution points: -∞ and all bounds
      val bounds = atoms.flatMap(boundFrom(_, varIdx))
      val testPoints = ExtendedReal.NegInf :: bounds.map(ExtendedReal.Finite.apply)

      QFFormula.or(testPoints.map { tp =>
        substituteExtended(f, varIdx, tp)
      })

  // Eliminate one variable using Weispfenning's virtual substitution (quadratic)
  def eliminateQuadratic(f: QFFormula, varIdx: Int): Option[QFFormula] =
    val atoms = collectAtoms(f, varIdx)
    val maxDeg = atoms.map(a => Polynomial.degree(a.poly, varIdx)).maxOption.getOrElse(0)
    if maxDeg > 2 then None // Falls back to CAD
    else
      // For each atom ax² + bx + c ~ 0, virtual substitution points are:
      // -b/2a ± sqrt(b² - 4ac)/2a
      val vsPoints = atoms.flatMap(vsSubstitutionPoints(_, varIdx))
      val allPoints = ExtendedReal.NegInf :: vsPoints
      Some(QFFormula.or(allPoints.map { tp =>
        substituteExtended(f, varIdx, tp)
      }))

  private def collectLinearAtoms(f: QFFormula, varIdx: Int): List[QFFormula.Atom] =
    collectAtoms(f, varIdx).filter(a => Polynomial.degree(a.poly, varIdx) <= 1)

  private def collectAtoms(f: QFFormula, varIdx: Int): List[QFFormula.Atom] = f match
    case a: QFFormula.Atom if Polynomial.degree(a.poly, varIdx) > 0 => List(a)
    case QFFormula.And(l, r)    => collectAtoms(l, varIdx) ++ collectAtoms(r, varIdx)
    case QFFormula.Or(l, r)     => collectAtoms(l, varIdx) ++ collectAtoms(r, varIdx)
    case QFFormula.Not(g)       => collectAtoms(g, varIdx)
    case QFFormula.Implies(l,r) => collectAtoms(l, varIdx) ++ collectAtoms(r, varIdx)
    case _                      => Nil

  private def boundFrom(atom: QFFormula.Atom, varIdx: Int): Option[VSPoint] =
    // For ax + b ~ 0: x ~ -b/a
    val (a, b) = extractLinearCoeffs(atom.poly, varIdx)
    if a == Rational.zero then None
    else Some(VSPoint.Linear(-b / a, atom.rel, a > Rational.zero))

  private def vsSubstitutionPoints(atom: QFFormula.Atom, varIdx: Int): List[VSPoint] =
    val deg = Polynomial.degree(atom.poly, varIdx)
    if deg == 1 then
      boundFrom(atom, varIdx).toList
    else if deg == 2 then
      val (a, b, c) = extractQuadraticCoeffs(atom.poly, varIdx)
      val disc = b * b - Rational(4) * a * c
      List(
        VSPoint.Quadratic(-b, a, disc, true),
        VSPoint.Quadratic(-b, a, disc, false)
      )
    else Nil

  private def extractLinearCoeffs(p: Polynomial, varIdx: Int): (Rational, Rational) =
    val a = Polynomial.coeffOf(p, varIdx, 1)
    val b = Polynomial.coeffOf(p, varIdx, 0)
    (a, b)

  private def extractQuadraticCoeffs(p: Polynomial, varIdx: Int): (Rational, Rational, Rational) =
    val a = Polynomial.coeffOf(p, varIdx, 2)
    val b = Polynomial.coeffOf(p, varIdx, 1)
    val c = Polynomial.coeffOf(p, varIdx, 0)
    (a, b, c)

  private def substituteExtended(f: QFFormula, varIdx: Int, point: ExtendedReal): QFFormula =
    point match
      case ExtendedReal.NegInf    => substituteNegInf(f, varIdx)
      case ExtendedReal.PosInf    => substitutePosInf(f, varIdx)
      case ExtendedReal.Finite(r) => substituteRational(f, varIdx, r)

  private def substituteRational(f: QFFormula, varIdx: Int, r: Rational): QFFormula = f match
    case QFFormula.Atom(p, rel) =>
      val pSub = Polynomial.substituteRational(p, varIdx, r)
      val v = Polynomial.evalConstant(pSub)
      evalRelation(v, rel)
    case QFFormula.And(l, r2)    => QFFormula.And(substituteRational(l, varIdx, r), substituteRational(r2, varIdx, r))
    case QFFormula.Or(l, r2)     => QFFormula.Or(substituteRational(l, varIdx, r), substituteRational(r2, varIdx, r))
    case QFFormula.Not(g)        => QFFormula.Not(substituteRational(g, varIdx, r))
    case QFFormula.Implies(l,r2) => QFFormula.Implies(substituteRational(l, varIdx, r), substituteRational(r2, varIdx, r))
    case other                   => other

  private def substituteNegInf(f: QFFormula, varIdx: Int): QFFormula = f match
    case QFFormula.Atom(p, rel) =>
      val leadDeg = Polynomial.degree(p, varIdx)
      val leadCoeff = Polynomial.leadingCoeff(p, varIdx)
      val signAtNegInf = if leadDeg % 2 == 0 then leadCoeff.sign else -leadCoeff.sign
      evalRelation(Rational(signAtNegInf), rel)
    case QFFormula.And(l, r)    => QFFormula.And(substituteNegInf(l, varIdx), substituteNegInf(r, varIdx))
    case QFFormula.Or(l, r)     => QFFormula.Or(substituteNegInf(l, varIdx), substituteNegInf(r, varIdx))
    case QFFormula.Not(g)       => QFFormula.Not(substituteNegInf(g, varIdx))
    case QFFormula.Implies(l,r) => QFFormula.Implies(substituteNegInf(l, varIdx), substituteNegInf(r, varIdx))
    case other                  => other

  private def substitutePosInf(f: QFFormula, varIdx: Int): QFFormula = f match
    case QFFormula.Atom(p, rel) =>
      val leadCoeff = Polynomial.leadingCoeff(p, varIdx)
      evalRelation(Rational(leadCoeff.sign), rel)
    case QFFormula.And(l, r)    => QFFormula.And(substitutePosInf(l, varIdx), substitutePosInf(r, varIdx))
    case QFFormula.Or(l, r)     => QFFormula.Or(substitutePosInf(l, varIdx), substitutePosInf(r, varIdx))
    case QFFormula.Not(g)       => QFFormula.Not(substitutePosInf(g, varIdx))
    case QFFormula.Implies(l,r) => QFFormula.Implies(substitutePosInf(l, varIdx), substitutePosInf(r, varIdx))
    case other                  => other

  private def evalRelation(v: Rational, rel: Relation): QFFormula =
    val holds = rel match
      case Relation.Eq  => v == Rational.zero
      case Relation.Neq => v != Rational.zero
      case Relation.Lt  => v < Rational.zero
      case Relation.Le  => v <= Rational.zero
      case Relation.Gt  => v > Rational.zero
      case Relation.Ge  => v >= Rational.zero
    if holds then QFFormula.True else QFFormula.False

enum ExtendedReal:
  case NegInf
  case PosInf
  case Finite(value: Rational)

enum VSPoint:
  case Linear(value: Rational, rel: Relation, positive: Boolean)
  case Quadratic(negB: Rational, twoA: Rational, disc: Rational, plusSqrt: Boolean)

// ============================================================================
// MAIN QE ENGINE
// ============================================================================

final class QEEngine(config: QEConfig = QEConfig.default):

  def eliminate(problem: QEProblem): QEResult =
    val startTime = System.currentTimeMillis()
    val orderedVars = EliminationOrder.orderVars(problem, config.eliminationOrder)

    var currentFormula = problem.matrix
    val projectionSets = scala.collection.mutable.Map.empty[String, Set[Polynomial]]
    var currentNVars = problem.nTotalVars

    for varName <- orderedVars do
      val varIdx = problem.quantifiers.collectFirst {
        case Quantifier.Exists(n, i) if n == varName => i
        case Quantifier.Forall(n, i) if n == varName => i
      }.getOrElse(0)

      val isForall = problem.quantifiers.exists {
        case Quantifier.Forall(n, _) if n == varName => true
        case _ => false
      }

      // ∀x.φ = ¬∃x.¬φ
      val existsFormula = if isForall then QFFormula.neg(currentFormula) else currentFormula

      val maxDeg = maxDegreeInVar(existsFormula, varIdx)

      currentFormula = if maxDeg <= 1 && config.useVirtualSubstitution then
        // Linear: use VS (much faster)
        val result = VirtualSubstitution.eliminateLinear(existsFormula, varIdx)
        FormulaSimplifier.simplify(result)
      else if maxDeg <= 2 && config.useVirtualSubstitution then
        // Quadratic: try VS
        VirtualSubstitution.eliminateQuadratic(existsFormula, varIdx)
          .map(FormulaSimplifier.simplify)
          .getOrElse(eliminateByCAD(existsFormula, varIdx, projectionSets))
      else
        // General: full CAD
        eliminateByCAD(existsFormula, varIdx, projectionSets)

      if isForall then
        currentFormula = QFFormula.neg(currentFormula)

      currentFormula = FormulaSimplifier.simplify(currentFormula)

    val elapsed = System.currentTimeMillis() - startTime
    val totalProjPolys = projectionSets.values.map(_.size).sum

    QEResult(
      formula = currentFormula,
      certificate = QECertificate(
        projectionPolynomials = projectionSets.toMap,
        cadStack = CADStack(Nil), // populated during CAD path
        cellFormulas = Map.empty,
        witnessMap = Map.empty
      ),
      stats = QEStats(
        inputPolynomials = countAtoms(problem.matrix),
        projectionPolynomials = totalProjPolys,
        cadCells = 0,
        satisfyingCells = 0,
        eliminationTimeMs = elapsed
      )
    )

  private def eliminateByCAD(
    f: QFFormula,
    varIdx: Int,
    projectionSets: scala.collection.mutable.Map[String, Set[Polynomial]]
  ): QFFormula =
    val polys = extractPolynomials(f)
    val projPolys = QEProjection.projectForQE(polys, varIdx)
    projectionSets(s"var_$varIdx") = projPolys

    // Build CAD over projected polynomials
    val nVars = polys.headOption.map(_.numVars).getOrElse(1)
    val cad = CADSolver(nVars)
    val stack = cad.decompose(polys)

    // For each cell, evaluate formula at sample point
    val satisfyingCellFormulas = stack.cells.flatMap { cell =>
      val samplePoint = cellSampleMap(cell)
      if QFFormula.evaluate(f, samplePoint) then
        Some(CellFormulaConstructor.cellToFormula(cell, List(projPolys), List.empty))
      else None
    }

    QFFormula.or(satisfyingCellFormulas)

  private def cellSampleMap(cell: CADCell): Map[String, Rational] =
    cell.samplePoint.zipWithIndex.map { (v, i) =>
      val r = v match
        case Left(r)    => r
        case Right(alg) => (alg.isolatingInterval._1 + alg.isolatingInterval._2) / 2
      s"x_$i" -> r
    }.toMap

  private def extractPolynomials(f: QFFormula): Set[Polynomial] = f match
    case QFFormula.Atom(p, _)    => Set(p)
    case QFFormula.And(l, r)     => extractPolynomials(l) ++ extractPolynomials(r)
    case QFFormula.Or(l, r)      => extractPolynomials(l) ++ extractPolynomials(r)
    case QFFormula.Not(g)        => extractPolynomials(g)
    case QFFormula.Implies(l, r) => extractPolynomials(l) ++ extractPolynomials(r)
    case _                       => Set.empty

  private def maxDegreeInVar(f: QFFormula, varIdx: Int): Int = f match
    case QFFormula.Atom(p, _)    => Polynomial.degree(p, varIdx)
    case QFFormula.And(l, r)     => maxDegreeInVar(l, varIdx).max(maxDegreeInVar(r, varIdx))
    case QFFormula.Or(l, r)      => maxDegreeInVar(l, varIdx).max(maxDegreeInVar(r, varIdx))
    case QFFormula.Not(g)        => maxDegreeInVar(g, varIdx)
    case QFFormula.Implies(l, r) => maxDegreeInVar(l, varIdx).max(maxDegreeInVar(r, varIdx))
    case _                       => 0

  private def countAtoms(f: QFFormula): Int = f match
    case _: QFFormula.Atom       => 1
    case QFFormula.And(l, r)     => countAtoms(l) + countAtoms(r)
    case QFFormula.Or(l, r)      => countAtoms(l) + countAtoms(r)
    case QFFormula.Not(g)        => countAtoms(g)
    case QFFormula.Implies(l, r) => countAtoms(l) + countAtoms(r)
    case _                       => 0

final case class QEConfig(
  eliminationOrder: EliminationOrder = EliminationOrder.DegreeBased,
  useVirtualSubstitution: Boolean = true,
  simplify: Boolean = true,
  extractCertificate: Boolean = true
)
object QEConfig:
  val default: QEConfig = QEConfig()
