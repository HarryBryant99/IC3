package cnf;

/**
 * Repraesentation von Variablen fuer aussagenlogische Formeln.
 * <p>
 * Diese Klasse stellt neben {@code toString}, {@code equals} und {@hashCode} 
 * kein oeffentliches Interface bereit.
 * Variablen koennen mit de Methode {@code freshVarName()} der
 * Klasse {@code CNF} konstruiert werden.
 */

public final class VarName {

  public int getNumber() {
    return number;
  }

  final int number;

  VarName() {
    this.number = CNF.freshName();
  }

  VarName(int n) {
    this.number = n;
  }

  @Override
  public String toString() {
    return "x" + number;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final VarName other = (VarName) obj;
    if (this.number != other.number) {
      return false;
    }
    return true;
  }

  @Override
  public int hashCode() {
    int hash = 7;
    hash = 79 * hash + this.number;
    return hash;
  }

}
