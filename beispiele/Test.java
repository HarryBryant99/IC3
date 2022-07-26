package beispiele;

import cnf.Formula;
import cnf.VarName;
import java.util.Set;
import static cnf.CNF.*;
import org.sat4j.specs.TimeoutException;

public class Test {

  public static void main(String[] args) throws TimeoutException {
    VarName x1 = freshVarName();
    VarName x2 = freshVarName();
    VarName x3 = freshVarName();
    VarName x4 = freshVarName();

//    (not d \/ c \/ not b \/ not a) /\ (b \/ not d \/ a \/ not c) /\ (b \/ c \/ a \/ d)
//	/\ a
//            /\ (c \/ not b)
//	/\ (d \/ not d)
//	/\ (c \/ not d)
//
//    and
//
//    (a /\ b /\ not d)

    Formula f = and(and(and(and(or(or(or(neg(var(x4)), var(x3)), neg(var(x2))), neg(var(x1))),
            or(or(or(var(x2), neg(var(x4))), var(x1)), neg(var(x3)))),
            or(or(or(var(x2), var(x3)), var(x1)), var(x4))),
            or(or(or(neg(var(x4)), var(x1)), var(x2)), var(x3))),
            or(or(or(neg(var(x1)), neg(var(x2))), neg(var(x3))), var(x4)));

    f = and(f, or(or(neg(var(x2)), var(x3)), var(x4)));

    System.out.println("Formula f: " + f);
    //System.out.println("Formula in CNF, with more variables: " + cnf(f));
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
