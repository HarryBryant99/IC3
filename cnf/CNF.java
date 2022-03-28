package cnf;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

/**
 * Methoden zur Konstruktion von aussagenlogischen
 * Formeln sowie zum Aufruf eines SAT-Solvers.
 * <p>
 * Diese Klasse ist das gesamte oeffentliche Interface des
 * Pakets {@code cnf}. Die anderen Klassen stellen kein
 * oeffentliches Interface bereit.
 */
public class CNF {

  // Diese Klasse sammelt nur statische Methoden; man benoetigt
  // keine Instanzen davon.
  private CNF() {
  }

  /**
   * Erzeugt die Formel, die durch eine aussagenlogische Variable
   * gegeben ist.
   *
   * @param  name Name der Variable
   */
  public static Formula var(VarName name) {
    if (name == null) {
      throw new NullPointerException("Variablenname darf nicht `null' sein!");
    }
    return new FormulaVar(name);
  }

  /**
   * Erzeugt die Negation einer gegbenen Formel.
   */
  public static Formula neg(Formula f) {
    return new FormulaNeg(f);
  }

  /**
   * Erzeugt die Konjunktion zweier Formeln.
   */
  public static Formula and(Formula f1, Formula f2) {
    List<Formula> fms = new LinkedList<Formula>();
    fms.add(f1);
    fms.add(f2);
    return new FormulaAnd(fms);
  }

  /**
   * Erzeugt die Konjunktion einer Liste von Formeln.
   */
  public static Formula and(List<Formula> fms) {
    return new FormulaAnd(fms);
  }

  /**
   * Erzeugt die Disjunktion zweier Formeln.
   */
  public static Formula or(Formula f1, Formula f2) {
    List<Formula> fms = new LinkedList<Formula>();
    fms.add(f1);
    fms.add(f2);
    return new FormulaOr(fms);
  }

  /**
   * Erzeugt die Disjunktion einer Liste von Formeln.
   */
  public static Formula or(List<Formula> fms) {
    return new FormulaOr(fms);
  }

  /**
   * Erzeugt die Implikation zweier Formeln.
   *
   * @param fm1 Formel
   * @param fm2 Formel
   * @return Formel "fm1 => fm2"
   */
  public static Formula imp(Formula fm1, Formula fm2) {
    return or(neg(fm1), fm2);
  }

  /**
   * Erzeugt die Biimplikation zweier Formeln.
   *
   * @param fm1 Formel
   * @param fm2 Formel
   * @return Formel "fm1 <=> fm2"
   */
  public static Formula iff(Formula fm1, Formula fm2) {
    return and(imp(fm1, fm2), imp(fm2, fm1));
  }

  /**
   * Erzeugt das exklusive Oder zweier Formeln.
   */
  public static Formula xor(Formula fm1, Formula fm2) {
    return or(and(fm1, neg(fm2)), and(neg(fm1), fm2));
  }

  /**
   * Gibt eine zur uebergebenen Formel erfuellbarkeitsaequivalente
   * Formel in CNF zurueck. 
   * <p>
   * Diese Methode kann zum Anzeigen der CNF einer Formel benutzt werden: 
   * {@code System.out.println(cnf(f))}.
   *
   * @param f Formel
   * @return Formel in CNF, welche zu f erfuellbarkeitsaequivalent ist.
   */
  public static Formula cnf(Formula f) {
    TseitinVisitor tseitinVisitor = new TseitinVisitor();
    Integer x = f.accept(tseitinVisitor);
    return tseitinVisitor.getResultFormula(x);
  }

  /**
   * Gibt eine zur uebergebenen Formel erfuellbarkeitsaequivalente
   * Formel in CNF als String im DIMACS zurueck.
   */
  public static String cnfDIMACS(Formula f) {
    TseitinVisitor tseitinVisitor = new TseitinVisitor();
    Integer x = f.accept(tseitinVisitor);
    return tseitinVisitor.getResultDIMACS(x);
  }

  /**
   * Wandelt die uebergebene Formel in eine erfuellbarkeitsaequivalente Formel
   * in CNF um und ueberprueft sie mittels des SAT-Solvers SAT4j auf Erfuellbarkeit.
   * 
   * Zurueckgegeben wird die Menge der wahren Variablen in einer erfuellenden
   * Belegung von {@ f} oder {@code null}, wenn es keine solche gibt.
   * 
   * @param f Formel
   * @throws TimeoutException
   * @return Menge der Variablen, die in einer erfuellenden Belegung
   *         von {@code f} wahr sind; oder {@code null} wenn {@code f}
   *         unerfuellbar ist.
   */
  public static Set<VarName> satisfiable(Formula f) throws TimeoutException {
    TseitinVisitor tseitinVisitor = new TseitinVisitor();
    Integer x = f.accept(tseitinVisitor);
    Set<Set<Integer>> clauses = tseitinVisitor.getClauses();

    int maxVar = nextName;

    ISolver solver = SolverFactory.newDefault();

    solver.newVar(maxVar);
    solver.setExpectedNumberOfClauses(clauses.size());
    try {
      solver.addClause(new VecInt(new int[]{x}));
      for (Set<Integer> c : clauses) {
        int[] carr = new int[c.size()];
        int i = 0;
        for (Integer y : c) {
          carr[i] = y;
          i++;
        }
        solver.addClause(new VecInt(carr));
      }
    } catch (ContradictionException ex) {
      return null; // unsat
    }

    IProblem problem = solver;
    if (problem.isSatisfiable()) {
      int[] model = problem.model();
      Set<VarName> trueVars = new HashSet<VarName>();
      for (Integer y : model) {
        if (y > 0) {
          trueVars.add(new VarName(y));
        }
      }
      return trueVars;
    } else {
      return null;
    }
  }

  /**
   * Erzeugt eine neue Variable.
   */
  public static VarName freshVarName() {
    return new VarName();
  }

  /**
   * Setzt den Variablennamengenerator zurueck.
   * Nach einem reset() sollte keine Formel mehr benutzt werden, die
   * davor erzeugt wurde.
   */
  public static void reset() {
    nextName = 1;
  }

  static int nextName = 1;

  static int freshName() {
    return nextName++;
  }


}
