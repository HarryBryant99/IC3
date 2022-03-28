package beispiele;

import cnf.Formula;
import cnf.VarName;
import java.util.Set;
import static cnf.CNF.*;
import org.sat4j.specs.TimeoutException;

public class Predecessor {

  public static void main(String[] args) throws TimeoutException {
    VarName a = freshVarName();
    VarName b = freshVarName();
    VarName c = freshVarName();
    VarName d = freshVarName();

    Formula c1 = or(neg(var(d)), or(var(c), or(neg(var(b)), neg(var(a)))));
    Formula c2 = or(neg(var(b)), or(neg(var(d)), or(var(a), neg(var(c)))));
    Formula c3 = or(var(b), or(var(c), or(var(a), var(d))));
    Formula c4 = or(var(c), neg(var(b)));
    Formula c5 = or(var(d), neg(var(b)));

    Formula c6 = or(neg(var(b)), var(c));
    Formula c7 = or(neg(var(b)), var(d));

    //((a /\ not b /\ not c /\ not d) \/ (a /\ b /\ c /\ d))
    Formula initial = or(and(var(a), and(neg(var(b)), and(neg(var(c)),neg(var(d))))),
            and(var(a), and(var(b), and(var(c),var(d)))));

    //Formula f = neg(and(and(c1,and(c2,and(c3,and(c4,c5)))),
    Formula f = and(and(c1,and(c2,and(c3,and(c6,c7)))),

            neg(and(neg(var(a)),and(neg(var(b)),neg(var(c))))));

    System.out.println("Formula f: " + f);
    System.out.println("Formula in CNF, with more variables: " + cnf(f));
    Set<VarName> trueVars = satisfiable(f);
    if (trueVars == null) {
      System.out.println("Not satisfiable");
    } else {
      System.out.print("Satisfiable," +
              " e.g. with an assignment that makes the following variables true" +
              "(and all others false): ");
      for (VarName v : trueVars) {
          System.out.print(v + " ");
      }
      System.out.println();
    }
    System.out.println("CNF of f, in DIMACS-Format:\n" + cnfDIMACS(f));
  }
}
