package cnf;

/**
 * Repraesentation aussagenlogischer Formeln.
 * <p>
 * Diese Klasse stellt neben {@toString} 
 * kein oeffentliches Interface bereit.
 * Formeln koennen mit den Methoden der Klasse {@code CNF}
 * konstruiert werden.
 */

public abstract class Formula {

  // package-private
  Formula() {}

  abstract <A> A accept(FormulaVisitor<A> visitor);

  /**
   * Wandelt die repraesentierte Formel in einen String um.
   */
  abstract public String toString();
}
