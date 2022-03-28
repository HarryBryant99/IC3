package cnf;

interface FormulaVisitor<A> {

  A visitVar(FormulaVar fm);

  A visitNeg(FormulaNeg fm);

  A visitOr(FormulaOr fm);

  A visitAnd(FormulaAnd fm);
}
