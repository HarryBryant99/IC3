package beispiele;

import cnf.Formula;
import cnf.VarName;
import java.util.Set;
import static cnf.CNF.*;
import org.sat4j.specs.TimeoutException;

public class Test {

  public static void main(String[] args) throws TimeoutException {
    VarName a = freshVarName();
    VarName b = freshVarName();
    VarName c = freshVarName();
    VarName d = freshVarName();

//    (not d \/ c \/ not b \/ not a) /\ (b \/ not d \/ a \/ not c) /\ (b \/ c \/ a \/ d)
//	/\ a
//            /\ (c \/ not b)
//	/\ (d \/ not d)
//	/\ (c \/ not d)
//
//    and
//
//    (a /\ b /\ not d)

    Formula f = and(and(or(neg(d), or(c, or(neg(b), neg(a)))), and(or(b, or(neg(d), or(a, neg(c)))), or(b, or(c, or(a,d))))),
            and(a,and(b,neg(d))));

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
