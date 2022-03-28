package cnf;

final class FormulaNeg extends Formula {

  final Formula fm;

  public FormulaNeg(Formula fm) {
    this.fm = fm;
  }

  <A> A accept(FormulaVisitor<A> visitor) {
    return visitor.visitNeg(this);
  }

  @Override
  public String toString() {
    return "neg(" + fm + ")";
  }

  @Override
  public boolean equals(Object obj) {
    if (obj == null) {
      return false;
    }
    if (getClass() != obj.getClass()) {
      return false;
    }
    final FormulaNeg other = (FormulaNeg) obj;
    if (this.fm != other.fm && (this.fm == null || !this.fm.equals(other.fm))) {
      return false;
    }
    return true;
  }

  @Override
  public int hashCode() {
    int hash = 5;
    hash = 37 * hash + (this.fm != null ? this.fm.hashCode() : 0);
    return hash;
  }
}


