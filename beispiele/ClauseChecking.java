package beispiele;

import cnf.Formula;
import cnf.VarName;

import java.util.Set;

import static cnf.CNF.*;

import org.sat4j.specs.TimeoutException;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.Scanner;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.io.IOException;
import java.util.stream.Collectors;

public class ClauseChecking {

    //The number of variables in the automaton (and their prime equivalents). Set to 4 as this is lowest amount
    private static short numberOfVars = 4;

    //ArrayList to store the variables created to represent those in the automaton
    private static ArrayList<VarName> vars = new ArrayList<>();

    /*List of Lists to store each of the Dimacs CNFs read in from the CNF files. For example, the formula (A or B) and C
    is written as 1 2 0 3 0 in Dimacs, and is stored as [[1,2],3]. There is a list for the initial states, the safety
    formula and the transitions.
     */
    private static List<List<Integer>> initialClauses = new ArrayList<>();
    private static List<List<Integer>> safetyClauses;
    private static List<List<Integer>> transitionClauses;

    //List of lists to store the clauses that make up the current Fk invariant formula
    private static List<List<Integer>> invariantClauses;

    //List of Lists to store all clauses in the inital formula but not in the safety formula in the initialisation phase
    private static List<List<Integer>> clausesToCheck = new ArrayList<List<Integer>>();

    //Array List to store all the invariant formulas produced
    private static ArrayList<Invariant> invariants = new ArrayList<>();

    private static Formula counterExample;
    private static Formula counterExamplePrimed;

    //List of integers to represent the counter example in numeric form
    private static List<Integer> counterClause = new ArrayList<Integer>();

    public static void main(String[] args) throws TimeoutException, IOException {
        //VarName variables created and added to the ArrayList
        for (int i = 0; i < numberOfVars; i++) {
            VarName x = freshVarName();
            vars.add(x);
        }

        ArrayList<Integer> newList = new ArrayList<Integer>();
        newList.add(1);
        newList.add(2);
        initialClauses.add(newList);

        Formula inv = or(var(vars.get(0)), var(vars.get(1)));
        Invariant newInv = new Invariant(inv);
        invariants.add(newInv);

        counterClause.add(1);
        counterClause.add(2);
        counterClause.add(-3);
        counterClause.add(-4);

        counterExample = and(neg(var(vars.get(0))), and(neg(var(vars.get(1))), and(var(vars.get(2)), var(vars.get(3)))));

        System.out.println("\n" + erroneousPhase(0));
    }

    private static boolean erroneousPhase(int counter) throws TimeoutException, IOException {
        /*  For all clauses c:
                If 3 conditions hold, add c to all Fk
                else add ¬s to all Fk
             */

        List<List<List<Integer>>> subclauses = getClause();
        System.out.println("Subclauses: " + subclauses.size());

        //do checks

        //F0 => ¬s
        //(F0 /\ s)
        Formula check1 = listToFormula(initialClauses, false, false);
        check1 = and(check1, counterExample);

        System.out.println(check1 + ": " + !isSatisfiable(check1));

        boolean subclauseFound = false;

        if (!isSatisfiable(check1)) {
            System.out.println("Passed Check 1");
            if (!subclauseFound) {
                for (int i = 0; i < subclauses.size(); i++) {
                    if (!subclauseFound) {
                        for (int j = 0; j < subclauses.get(i).size(); j++) {
                            System.out.println("\n" + subclauses.get(i).get(j));
                            //c must be negated

                            //Fk /\ c
                            Formula check2 = invariants.get(counter).getInvariant();
                            check2 = and(check2,
                                    neg(clauseToFormula(subclauses.get(i).get(j), false, false)));

                            if (!isSatisfiable(check2)) {
                                System.out.println("Passed Check 2");

                                // c subset ¬s
                                //s ∧ ¬c
                                Formula check3 = counterExample;
                                check3 = and(check3,
                                        clauseToFormula(subclauses.get(i).get(j), false, false));

                                if (!isSatisfiable(check3)) {
                                    System.out.println("Passed Check 3");
                                    subclauseFound = true;
                                    counterClause = subclauses.get(i).get(j);
                                    break;
                                } else {
                                    System.out.println("Failed Check 3");
                                }
                            } else {
                                System.out.println("Failed Check 2");
                            }
                        }
                    }
                }
            }
        }

        System.out.println("\n"+ counterClause);
        return subclauseFound;
    }

    private static boolean isSatisfiable(Formula f) throws TimeoutException {
        //Overwritten if the formula is satisfiable
        boolean satisfiable = false;

        //Calls the SAT-Solver, produces a set of counter example variables if it is satisfiable, otherwise the set is empty
        Set<VarName> trueVars = satisfiable(f);
        if (trueVars == null) {
            System.out.println("Not satisfiable");
        } else {
            System.out.print("Satisfiable," +
                    " e.g. with an assignment that makes the following variables true" +
                    "(and all others false): ");

            System.out.println();

            //Return true
            satisfiable = true;
        }
        return satisfiable;
    }

    private static List<List<List<Integer>>> getClause(){
        CombinationFinder cf = new CombinationFinder();

        List<List<List<Integer>>> subclauses = new ArrayList<>();

        for (int i = 1; i < counterClause.size(); i++) {
            List<List<Integer>> newSubclause = cf.printCombination(counterClause, counterClause.size(), i);
            subclauses.add(newSubclause);
            System.out.println(newSubclause);
        }

        return subclauses;

//        List<Formula> clauseFormulas = new ArrayList<>();
//        clauseFormulas.add(clauseToFormula(counterClause.subList(counter, counter+length),false,false));
//        clauseFormulas.add(clauseToFormula(counterClause.subList(counter, counter+length),false,true));
//        return clauseFormulas;
    }

    private static Formula clauseToFormula(List<Integer> clauseParsed, boolean negateFormula, boolean isPrimed){
        //Test formula to instantiate the new clause
        Formula clause = or(var(vars.get(0)), var(vars.get(1)));

        //Loops through each element in the list of integers to create the clause
        for (int i = 0; i < clauseParsed.size(); i++) {

            //Boolean to state whether the element is already a negative, and therefore should be stored as a negative
            boolean negative = false;

            //If the element read from the Dimacs file is less than 0, then the corresponding variable negative
            if (clauseParsed.get(i) < 0) {
                negative = true;
            }

      /* Absolute value taken from the clause to avoid null pointer exceptions when loading the corresponding variable
      from the ArrayList
       */
            int pos = (Math.abs(clauseParsed.get(i))) - 1;

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

    private static Formula createClause(List<List<Integer>> clauses, boolean negateFormula, boolean isPrimed, int j) {
        //Test formula to instantiate the new clause
        Formula clause = or(var(vars.get(0)), var(vars.get(1)));

        //The new clause is returned so it can be combined with any others to form the complete formula
        return clauseToFormula(clauses.get(j), negateFormula, isPrimed);
    }
}