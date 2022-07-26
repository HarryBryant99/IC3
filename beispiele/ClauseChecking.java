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

public class IC3WithClauseGrouping {

    //The number of variables in the automaton (and their prime equivalents). Set to 4 as this is lowest amount
    private static short numberOfVars = 4;

    //ArrayList to store the variables created to represent those in the automaton
    private static ArrayList<VarName> vars = new ArrayList<>();

    /*List of Lists to store each of the Dimacs CNFs read in from the CNF files. For example, the formula (A or B) and C
    is written as 1 2 0 3 0 in Dimacs, and is stored as [[1,2],3]. There is a list for the initial states, the safety
    formula and the transitions.
     */
    private static List<List<Integer>> initialClauses;
    private static List<List<Integer>> safetyClauses;
    private static List<List<Integer>> transitionClauses;

    //List of lists to store the clauses that make up the current Fk invariant formula
    private static List<List<Integer>> invariantClauses;

    //List of Lists to store all clauses in the inital formula but not in the safety formula in the initialisation phase
    private static List<List<Integer>> clausesToCheck = new ArrayList<List<Integer>>();

    //Array List to store all the invariant formulas produced
    private static ArrayList<Invariant> invariants = new ArrayList<>();

    public static void main(String[] args) throws TimeoutException, IOException {
        Formula inv =

        erroneousPhase(0);
    }

    private static boolean erroneousPhase(int counter) throws TimeoutException, IOException {
        /*  For all clauses c:
                If 3 conditions hold, add c to all Fk
                else add ¬s to all Fk
             */

        List<List<List<Integer>>> subclauses = getClause();
        System.out.println("Subclauses: " + subclauses.size());

        //do checks

        //(F0 /\ s)
        Formula check1 = listToFormula(initialClauses, false, false);
        check1 = and(check1, counterExample);

        if (!isSatisfiable(check1)) {
            for (int i = 0; i < subclauses.size(); i++) {
                for (int j = 0; j < subclauses.get(i).size(); j++) {
                    System.out.println("Passed 1");
                    //c must be negated

                    //Fk /\ c
                    Formula check2 = invariants.get(counter).getInvariant();
                    check2 = and(check2,
                            neg(clauseToFormula(subclauses.get(i).get(j), false, false)));

                    if (!isSatisfiable(check2)) {
                        System.out.println("Passed 2");

                        //¬s ∧ ¬c
                        Formula check3 = neg(counterExample);
                        check3 = and(check3,
                                clauseToFormula(subclauses.get(i).get(j), false, false));

                        if (!isSatisfiable(check3)) {
                            System.out.println("Passed 3");
                        } else {
                            System.out.println("Failed 3");
                        }
                    } else {
                        System.out.println("Failed 2");
                    }
                }
            }
        }
    }
}