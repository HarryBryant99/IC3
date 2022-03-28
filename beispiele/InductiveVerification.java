package beispiele;

import cnf.Formula;
import cnf.VarName;
import java.util.Set;
import static cnf.CNF.*;
import org.sat4j.specs.TimeoutException;


import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.Scanner;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.io.IOException;
import java.util.stream.Collectors;

public class InductiveVerification {
  private static short numberOfVars = 8;
  private static ArrayList<VarName> vars = new ArrayList<>();

  private static List<List<Integer>> initialClauses;
  private static List<List<Integer>> safetyClauses;
  private static List<List<Integer>> transitionClauses;

  private static Formula safety;

  public static void main(String[] args) throws TimeoutException, IOException{
    for (int i = 0; i < numberOfVars; i++) {
      VarName x = freshVarName();
      vars.add(x);
    }

    System.out.println("Inductive Verification\n");

    //Formula f = or(and(var(x1), var(x2)), and(var(x3), var(x4)));

    //Formula f = listToFormula(readCNF("D:\\University\\Project\\CNFs\\javaCNF\\beispiele\\Files\\safety.cnf"));

    initialClauses = readCNF("D:\\University\\Project\\CNFs\\javaCNF\\beispiele\\Files\\initial3.cnf");
    safetyClauses = readCNF("D:\\University\\Project\\CNFs\\javaCNF\\beispiele\\Files\\safety3.cnf");
    transitionClauses = readCNF("D:\\University\\Project\\CNFs\\javaCNF\\beispiele\\Files\\transitions3.cnf");

    System.out.println("Check: I /\\ !P");
    Formula f = listToFormula(initialClauses, false, false);
    f = and(f, neg(listToFormula(safetyClauses, false, false)));

    if (isSatisfiable(f)) {
      System.out.println("Initial states are not safe");
    } else {
      System.out.println("Initial states are safe");

      System.out.println("Check: T /\\ !P'");
      f = listToFormula(transitionClauses, false, false);
      f = and(f, neg(listToFormula(safetyClauses, false, true)));

      if (isSatisfiable(f)) {
        System.out.println("Transitions states are not safe");
      } else {
        System.out.println("Transitions states are safe");
      }
    }
  }

  private static boolean isSatisfiable(Formula f) throws TimeoutException{
    boolean satisfiable = false;
    System.out.println("Formula f: " + f);
//    System.out.println("Formula in CNF, with more variables: " + cnf(f));
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

      satisfiable = true;
    }
    //System.out.println("CNF of f, in DIMACS-Format:\n" + cnfDIMACS(f));
    return satisfiable;
  }

  private static List<List<Integer>> readCNF(String filename) throws IOException{
    final List<List<Integer>> clauses = Files.lines(Paths.get(filename))
            // Trim the lines:
            .map(line -> line.trim().replaceAll("\\s+", " ").trim())
            // Only parse lines ending with a 0:
            .filter(line -> line.endsWith(" 0"))
            // Turn each line into a list of integers:
            .map(line -> Arrays.stream(line
                    .substring(0, line.length() - 2)
                    .trim().split("\\s+"))
                    .map(Integer::parseInt)
                    .collect(Collectors.toList())
            ).collect(Collectors.toList());
    return clauses;
  }

  private static Formula listToFormula(List<List<Integer>> clauses, boolean negateFormula, boolean isPrimed) {
    //Test formula to instantiate the new formula
    Formula newFormula = or(var(vars.get(0)), var(vars.get(1)));

    //Creates a new clause for each list of lists passed in
    for (int j = 0; j < clauses.size(); j++) {
      //Calls method to produce the formula for the clause at j, again stating if negated or primed
      Formula clause = createClause(clauses, negateFormula, isPrimed, j);

      //If j = 0 overwrite the existing formula, otherwise formula because the existing formula and the new clause
      if (j == 0) {
        newFormula = clause;
      } else {
        newFormula = and(newFormula, clause);
      }
    }
    //Returns the completed formula
    return newFormula;
  }

  /**
   * Loops through each element in each list of integers, creating a formula that is each element connected by a logical
   * or. For example element 1 or element 2
   *
   * @param clauses       The list of list of integers representing a formula ready to be converted
   * @param negateFormula Boolean value stating whether the formula should be negated
   * @param isPrimed      Boolean value stating whether the formula should be a primed formula
   * @param j             The current position in the list of lists
   * @return The new clause as a formula
   */
  private static Formula createClause(List<List<Integer>> clauses, boolean negateFormula, boolean isPrimed, int j) {
    //Test formula to instantiate the new clause
    Formula clause = or(var(vars.get(0)), var(vars.get(1)));

    //Loops through each element in the list of integers to create the clause
    for (int i = 0; i < clauses.get(j).size(); i++) {

      //Boolean to state whether the element is already a negative, and therefore should be stored as a negative
      boolean negative = false;

      //If the element read from the Dimacs file is less than 0, then the corresponding variable negative
      if (clauses.get(j).get(i) < 0) {
        negative = true;
      }

      /* Absolute value taken from the clause to avoid null pointer exceptions when loading the corresponding variable
      from the ArrayList
       */
      int pos = (Math.abs(clauses.get(j).get(i))) - 1;

      //System.out.println(clauses.get(j).get(i));

      /*If formula is too be primed, the variables need to be from the second half of the list. This adds half the
      number of variables to the position value of the element to convert it to it to the primed equivalent
       */
      if (isPrimed) {
        pos += numberOfVars / 2;
      }

      /*The formula should add the negative version of the variable if one of the following conditions hold:
      1. The variable is already negative and the formula itself shouldn't be negated
      2. The variable is positive and the formula itself needs negating
      Otherwise the positive version is added to the formula
       */
      if ((negative && !negateFormula) || (!negative && negateFormula)) {
        //Negate variable
        //If the clause is empty set the clause to the element, otherwise add the element via a logical or
        if (i == 0) {
          clause = neg(var(vars.get(pos)));
        } else {
          clause = or(clause, neg(var(vars.get(pos))));
        }
      } else {
        //If the clause is empty set the clause to the element, otherwise add the element via a logical or
        if (i == 0) {
          clause = var(vars.get(pos));
        } else {
          clause = or(clause, var(vars.get(pos)));
        }
      }
    }
    //The new clause is returned so it can be combined with any others to form the complete formula
    return clause;
  }
}
