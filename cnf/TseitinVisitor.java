package cnf;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import static cnf.CNF.*;

class TseitinVisitor implements FormulaVisitor<Integer> {

  Map<Formula, Integer> fmVars;
  Set<Set<Integer>> clauses;

  TseitinVisitor() {
    fmVars = new HashMap<Formula, Integer>();
    clauses = new HashSet<Set<Integer>>();
  }

  Set<Set<Integer>> getClauses() {
    return clauses;
  }

  Formula getResultFormula(Integer x) {
    List<Formula> clfms = new LinkedList<Formula>();
    clfms.add(var (new VarName(x)));
    for (Set<Integer> c : clauses) {
      List<Formula> lits = new LinkedList<Formula>();
      for (Integer y : c) {
        if (y > 0) {
          lits.add(var(new VarName(y)));
        } else {
          lits.add(neg(var(new VarName(-y))));
        }
      }
      clfms.add(or(lits));
    }
    return and(clfms);
  }

  String getResultDIMACS(Integer x) {
    StringBuffer s = new StringBuffer();
    s.append("fm " + (clauses.size() + 1) + " " + nextName + "\n");
    s.append(x + " 0\n");
    for (Set<Integer> c : clauses) {
      for (Integer y : c) {
        s.append(y);
        s.append(" ");
      }
      s.append("0\n");
    }
    return s.toString();
  }

  public Integer visitVar(FormulaVar fm) {
    fmVars.put(fm, fm.name.number);
    return fm.name.number;
  }

  public Integer visitNeg(FormulaNeg fm) {
    Integer xbody = fmVars.get(fm.fm);
    if (xbody == null) {
      xbody = fm.fm.accept(this);
    }
    Integer x = freshName();
    fmVars.put(fm, x);
    Set<Integer> clause = new TreeSet<Integer>();
    clause.add(x);
    clause.add(xbody);
    clauses.add(clause);
    clause = new TreeSet<Integer>();
    clause.add(-x);
    clause.add(-xbody);
    clauses.add(clause);
    return x;
  }

  public Integer visitOr(FormulaOr fm) {
    List<Integer> xs = new LinkedList<Integer>();
    for (Formula f : fm.fms) {
      Integer x = fmVars.get(f);
      if (x == null) {
        x = f.accept(this);
      }
      xs.add(x);
    }
    Integer x = freshName();
    fmVars.put(fm, x);

    Set<Integer> clause = new TreeSet<Integer>();
    clause.add(-x);
    clause.addAll(xs);
    clauses.add(clause);

    for (Integer y : xs) {
      clause = new TreeSet<Integer>();
      clause.add(x);
      clause.add(-y);
      clauses.add(clause);
    }

    return x;
  }

  public Integer visitAnd(FormulaAnd fm) {
    List<Integer> xs = new LinkedList<Integer>();
    for (Formula f : fm.fms) {
      Integer x = fmVars.get(f);
      if (x == null) {
        x = f.accept(this);
      }
      xs.add(x);
    }
    Integer x = freshName();
    fmVars.put(fm, x);

    Set<Integer> clause = new TreeSet<Integer>();
    clause.add(x);
    for (Integer y : xs) {
      clause.add(-y);
    }
    clauses.add(clause);

    for (Integer y : xs) {
      clause = new TreeSet<Integer>();
      clause.add(-x);
      clause.add(y);
      clauses.add(clause);
    }

    return x;
  }
}

