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

/**
 * IC3.java
 *
 * @author Harry Bryant, using the code developed by Institute for Theoretical Computer Science at the LMU in Munich
 * <p> Copyright: No copyright </p>
 * <p> Version History:
 * Version 1: Initialisation Phase implemented,
 * Version 2: Holding Phase implemented,
 * Version 3: Erroneous Phase Implemented,
 * Version 3.1: Comments </p>
 * <p>
 * The class reads in 3 files containing CNFs in Dimacs form that represent an automaton. These are the initial states,
 * the transitions in the system and the safety formula. The purpose is to produce an Invariant formula for use in
 * Inductive Verification following the IC3 algorithm developed by Aaron Bradley. There are two main phases that to
 * achieve this:
 *
 * Initialisation Phase:
 * Checks that the intial states are safe, and that they transition to safe states. If these don't hold then the safety
 * formula is incorrect or an invariant will not be effective. Providing these hold, each clause c in the initial
 * formula, providing it is not already a clause in the safety formula, is checked via I /\ T => c'. If this holds then
 * it is added to the safety formula to produce an invariant formula F2.
 *
 * Iteration Phase:
 * Checks if the latest invariant formula Fk holds with the safety property by checking if Fk /\ T => P' holds. If it
 * does then the program goes to the holding phase to add further states to form Fk+1. Otherwise it goes to the holding
 * phase to remove the counter example produced by the SAT-Solver. By of these phases return to check if FK = Fk+1, if
 * this is the case then the invariant is found, otherwise the process repeats.
 * </p>
 * @version 3.1
 * <p> Creation Date: 14/03/21 </p>
 * <p> Last Modification Date: 25/03/21 </p>
 */
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

    //Path to where the files read and written to are kept
    private static String path = "D:\\University\\Project\\CNFs\\javaCNF\\beispiele\\Files\\";

    //String to store the name of the file containing the safety property
    private static String safetyFile;

    //The previously produced invariant formula to be compared to
    private static Formula invariantOld;

    //The new invariant formula compare the old formula to
    private static Formula invariantNew;

    /* When Fk /\ T => P' doesn't hold, the SAT-Solver produces a counter example, this formula is stored as both a
    standard formula and a primes equivlant
     */
    private static Formula counterExample;
    private static Formula counterExamplePrimed;

    //List of integers to represent the counter example in numeric form
    private static List<Integer> counterClause = new ArrayList<Integer>();

//  do{
//    invariantNew = listToFormula(safetyClauses,false, false);
//    Holding or Erroneous
//    invariantOld = invariantNew;
//  }while(invariantNew != invariantOld)

    /**
     * Reads in the files, creates the required number of variables and starts the initialisation phase. If this holds,
     * then the invariant found is set as the exisiting invariant and the iteration phase is started
     *
     * @param args
     * @throws TimeoutException
     * @throws IOException
     */
    public static void main(String[] args) throws TimeoutException, IOException {
        System.out.println("IC3\n");

        path = System.getProperty("user.dir");
        path = path + "\\beispiele\\Files\\";
        System.out.println("current dir = " + path);

        //Read in the Dimacs CNFs
        initialClauses = readCNF(path + "initial3.cnf");
        safetyFile = path + "safety3.cnf";
        safetyClauses = readCNF(safetyFile);
        transitionClauses = readCNF(path + "transitions3.cnf");

    /*Loop through all the elements in each of the transition clauses, finding the absolute max. This indicates how
    many VarName variables are needed in the system
     */
        for (int i = 0; i < transitionClauses.size(); i++) {
        for (int j = 0; j < transitionClauses.get(i).size(); j++) {
            if (numberOfVars < Math.abs(transitionClauses.get(i).get(j))) {
                //Short value of the new largest value
                numberOfVars = transitionClauses.get(i).get(j).shortValue();
            }
        }
    }

    //VarName variables created and added to the ArrayList
        for (int i = 0; i < numberOfVars; i++) {
        VarName x = freshVarName();
        vars.add(x);
    }

        System.out.println(numberOfVars + " variables created\n");

    //Initialsation phase called, the result is stored so that if this fails the iteration phase isn't run
    boolean initialisationHolds = initialisation();

    //Formula equivalent of the clauses generated from the initialisation phase saved as the first invariant
    invariantOld = listToFormula(invariantClauses, false, false);
        System.out.println("Old: " + invariantOld);
    //New Invariant type created and stored in the ArrayList
    Invariant f1 = new Invariant(invariantOld);
        invariants.add(f1);

    //Old invariant saved to file or future use
    saveInvariant(invariantClauses, "f1");

        System.out.println("Iteration Phase\n");

    //Iteration phase only takes place if the the initialisation phase was successful
        if (initialisationHolds) {
        iterationPhase(initialisationHolds);
    }
}

    /**
     * Calls the SAT-solver with the Formula passed in as the parameter, returns if the result was satisfiable or if it
     * was unsatisfiable
     *
     * @param f The formula to be checked
     * @return True if satisfiable, False if satisfiable
     * @throws TimeoutException
     */
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

    /**
     * Calls the SAT-solver with the Formula passed in as the parameter, returns if the result was satisfiable or if it
     * was unsatisfiable. If the result is satisfiable, the method produces a list of variables that hold in the counter
     * example - these must be in the in the range of variables defined at the start of the program. All over non-prime
     * variables are then false by default, these are combined to produce a counter example formula that can be added to
     * the invariants during the erroneous phase
     *
     * @param f The formula to be checked
     * @return True if satisfiable, False if satisfiable
     * @throws TimeoutException
     */
    private static boolean invariantHolds(Formula f) throws TimeoutException {
        //Overwritten if the formula is satisfiable
        boolean satisfiable = false;

        //Extra print statements for testing
//    System.out.println("Formula f: " + f);
//    System.out.println("Formula in CNF, with more variables: " + cnf(f));

        //Calls the SAT-Solver, produces a set of counter example variables if it is satisfiable, otherwise the set is empty
        Set<VarName> trueVars = satisfiable(f);
        if (trueVars == null) {
            System.out.println("Not satisfiable");
        } else {
            System.out.print("Satisfiable," +
                    " e.g. with an assignment that makes the following variables true" +
                    "(and all others false): ");

            //Variable to store the integer pointers to the counter example variables produced by the SAT-Solver
            ArrayList<Integer> counterVars = new ArrayList<Integer>();

            //Formula to represent the counter example
            Formula counterFormula = null;

            //Formula to represent the primed version of the counter example
            Formula counterFormulaPrime = null;

            //Clear any existing clauses from previous iterations
            counterClause.clear();

            //Loop through all variables produced by the SAT-Solver
            for (VarName v : trueVars) {
                //Only variables that in in the range of the existing non-primed variables can be included
                if (v.getNumber() <= (numberOfVars / 2)) {
                    System.out.print(v + " ");
                    //Integer added to the ArrayList, number - 1 used to counter the off by one error as the Arrays start at 0
                    counterVars.add(v.getNumber() - 1);

                    //If Formula is emtpy, set it to equal the element otherwise add to it
                    if (counterFormula == null) {
                        counterFormula = var(vars.get(v.getNumber() - 1));
                        counterFormulaPrime = var(vars.get((v.getNumber() - 1) + (numberOfVars / 2)));

                        counterClause.add(-(v.getNumber()));
                    } else {
                        counterFormula = and(counterFormula, var(vars.get(v.getNumber() - 1)));
                        counterFormulaPrime = and(counterFormulaPrime, var(vars.get((v.getNumber() - 1) + (numberOfVars / 2))));

                        counterClause.add(-(v.getNumber()));
                    }
                }
            }

            System.out.println();

      /* Loops through the list of variables, adding the negative version of those that are not already in the list as
      positive variables. This is because the counter example produces all the variables that are true, and all others
      are false
       */
            for (int i = 0; i < (numberOfVars / 2); i++) {
                boolean isCounterVar = false;
                for (int j = 0; j < counterVars.size(); j++) {
                    if (i == counterVars.get(j)) {
                        isCounterVar = true;
                    }
                }

                //If it is not in the list, add it to the formulas and clause
                if (!isCounterVar) {
                    counterFormula = and(counterFormula, neg(var(vars.get(i))));
                    counterFormulaPrime = and(counterFormulaPrime, neg(var(vars.get(i + (numberOfVars / 2)))));

                    counterClause.add(i + 1);
                }
            }

            //Outputs for testing
//      System.out.println("Counter Example: " + counterFormula);
            counterExample = counterFormula;
//
//      System.out.println("Counter Example Primed: " + counterFormulaPrime);
            counterExamplePrimed = counterFormulaPrime;

//      System.out.println(counterClause);

            //Return true
            satisfiable = true;
        }
//    System.out.println("CNF of f, in DIMACS-Format:\n" + cnfDIMACS(f));
        return satisfiable;
    }

    /**
     * Reads in a Dimacs CNF file, taken from https://www.royvanrijn.com/blog/2019/11/sat-solver-in-java/
     *
     * @param filename
     * @return A list containing a list of integers
     * @throws IOException
     */
    private static List<List<Integer>> readCNF(String filename) throws IOException {
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

    /**
     * Loops through each list of lists, producing a formula that has each one joined by a logical 'and'. For example,
     * list 1 and list 2 and so on
     *
     * @param clauses       The list of list of integers representing a formula ready to be converted
     * @param negateFormula Boolean value stating whether the formula should be negated
     * @param isPrimed      Boolean value stating whether the formula should be a primed formula
     * @return The formula computed
     */
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

        //The new clause is returned so it can be combined with any others to form the complete formula
        return clauseToFormula(clauses.get(j), negateFormula, isPrimed);
    }

    /**
     * The intialisation phase checks that I => P holds and that I /\ T => P' holds. If either of these fail then it means
     * either that the safety property is incorrect or that the automaton can't transition from the initial states without
     * becoming unsafe.
     * After this it does the first iteration where each clause c in the initial states, that isn't already a clause in
     * the safety property, is checked if it holds via I /\ T => c'. If a clause holds it is added to the safety property
     * to form the invariant F1
     *
     * @return Returns true if both checks pass then true is returned, if any fail false is returned to stop the program
     * entering the iteration phase
     * @throws TimeoutException
     * @throws IOException
     */
    private static boolean initialisation() throws TimeoutException, IOException {
        System.out.println("Initialisation Phase\n");

        //Formula constructed to check I => P, rearranged to be in CNF form: (I /\ ¬P)
        System.out.println("Check: I /\\ !P");
        Formula f = listToFormula(initialClauses, false, false);
        f = and(f, neg(listToFormula(safetyClauses, false, false)));

        //Boolean variable to state whether the checks in the initialisation phase have been successful, set to false if not
        boolean holds = true;

        //If (I /\ ¬P) is satisfiable then the initialisation phase doesn't hold. Otherwise it continues
        if (isSatisfiable(f)) {
            System.out.println("Initial states are not safe\n");
            //False to be returned as the first check hasn't held.
            holds = false;
        } else {
            System.out.println("Initial states are safe\n");

            //Formula constructed to check I /\ T => P, rearranged to be in CNF form: (I /\ T /\ ¬P')
            System.out.println("Check: I /\\ T /\\ !P'");
            f = listToFormula(initialClauses, false, false);
            f = and(f, listToFormula(transitionClauses, false, false));
            f = and(f, neg(listToFormula(safetyClauses, false, true)));

            //If (I /\ T /\ ¬P') is satisfiable then the initialisation phase doesn't hold. Otherwise it continues
            if (isSatisfiable(f)) {
                System.out.println("(I /\\ T) => P' doesn't hold\n");
                //False to be returned as the second check hasn't held.
                holds = false;
            } else {
                System.out.println("(I /\\ T) => P' holds\n");

                /*List of List of Integers returned containing all the clauses in the initial states that aren't already
                in the 7 safety property's clauses
                */
                clausesToCheck = checkExistingClauses();

                //The clauses for F1 set to the safety property ready to be added to
                invariantClauses = readCNF(safetyFile);

                /* Loop through all the clauses, checking if (I /\ T /\ ¬c') holds for each. If so, the clause is added
                to the clauses that form the invariant F1
                 */
                for (int j = 0; j < clausesToCheck.size(); j++) {
                    f = listToFormula(initialClauses, false, false);
                    f = and(f, listToFormula(transitionClauses, false, false));

                    //Clause converted into a formula for use in SAT-Solver
                    Formula clause = createClause(clausesToCheck, false, true, j);
                    System.out.println(clause);

                    //Formula to be checked: I /\ T /\ ¬c'
                    f = and(f, neg(clause));

                    //If (I /\ T /\ ¬c') is unsatisfiable then c is added to the list of clauses for F1
                    if (isSatisfiable(f)) {
                        System.out.println("Doesn't Hold\n");
                    } else {
                        System.out.println("Holds\n");
                        invariantClauses.add(clausesToCheck.get(j));
                    }
                }
            }
        }
        //Whether the initialisation phase passed the first 2 checks is returned
        return holds;
    }

    /**
     * Checks all the clauses in the initial states, adding all that are not clauses in the safety property to the list
     *
     * @return The new list of clauses in the initial states but not the safety property
     * @throws IOException
     */
    private static List<List<Integer>> checkExistingClauses() throws IOException {
        //How many clauses need checking against
        int numberOfClauses = initialClauses.size();

        //Any exisiting clauses cleared
        clausesToCheck.clear();

        /*Loops through each clause in the initial states, checking if it is in the safety property's clauses. If so the
        boolean value exisiting is set to true. Otherwise remains false
         */
        for (int i = 0; i < numberOfClauses; i++) {
            boolean existing = false;
            for (int j = 0; j < safetyClauses.size(); j++) {
                if (initialClauses.get(i) == safetyClauses.get(j)) {
                    existing = true;
                }
            }

            //If a unique clause, add it to the list
            if (!existing) {
                clausesToCheck.add(initialClauses.get(i));
            }
        }
        System.out.println(clausesToCheck);
        //Returns all the clauses in the new list
        return clausesToCheck;
    }

    /**
     * Checks if each clause c in the invariant holds under the invariant by using Fk /\ T => c'. If the clause holds then
     * it is added to from the new invariant that is returned to the iteration phase
     *
     * @param fk The previously computed invariant as a list of clauses
     * @return Returns a new invariant as a list of clauses
     * @throws TimeoutException
     */
    private static List<List<Integer>> holdingPhase(List<List<Integer>> fk) throws TimeoutException {
        System.out.println(fk);

        //Current invariant converted to a formula for use in each check
        final Formula fkFormula = listToFormula(fk, false, false);

        //Number of clauses in the old invariant
        int clausesInFk = fk.size();

        /*Loops through each clause in the old invariant, checking if (Fk /\ T /\ ¬c') holds for each. If so, the
        clause is added to the clauses that form the invariant Fk+1
         */
        for (int j = 0; j < clausesInFk; j++) {
            Formula f = and(fkFormula, listToFormula(transitionClauses, false, false));

            //Clause converted into a formula for use in SAT-Solver
            Formula clause = createClause(fk, false, true, j);

            //System.out.println("\n" + f + "\n");
            System.out.println("Checking: " + clause);

            //Formula set to Formula /\ ¬c
            f = and(f, neg(clause));

            //If (Fk /\ T /\ ¬c') is unsatisfiable then c is added to the list of clauses for Fk+1
            if (isSatisfiable(f)) {
                //invariantClauses.remove(j);
                System.out.println("Doesn't Hold\n");
            } else {
                fk.add(fk.get(j));
                System.out.println("Holds\n");
            }
        }

        //Remove all the clauses from the previous invariant
        for (int i = 0; i < clausesInFk; i++) {
            fk.remove(0);
        }
        //Return the new invariant as a list of clauses
        return fk;
    }

    /**
     * The iteration phase firstly checks if the safety property holds when a transition takes place from the old
     * invariant. If so then the program goes to the holding phase to produce a new invariant to add increase the number
     * of states that hold. If it doesn't hold the program goes to the erroneous phase (in this method) to remove the
     * counter example state and allow it to pass.
     * The iteration phase runs until the old invariant is the same as the new invariant. When this occurs the new
     * invariant is the one that should be used in to allow Inductive Verification to pass
     *
     * @param initialisationHolds
     * @throws TimeoutException
     * @throws IOException
     */
    private static void iterationPhase(boolean initialisationHolds) throws TimeoutException, IOException {
        //Counts the number of iterations that have taken place
        int counter = 0;

        /*invariant equal set to false, if the old invariant is the same as the new one then it is set to true so that
        the loop ends
         */
        boolean invariantsEqual = false;

        //Do-while loop runs until the old and new invariants are equal
        do {
            System.out.println("Iteration " + (counter + 1) + "\n");
            System.out.println("Fk: " + invariantClauses);

            /*Check that ¬(Fk /\ T => P'). If it is satisfiable then the program moves to the erroneous phase, otherwise
            go to the holding phase. Formula converted to CNF: Fk /\ T /\ ¬P'
             */
            System.out.println("Check: Fk /\\ T /\\ !P'");
            Formula f = invariants.get(counter).getInvariant();
            f = and(f, listToFormula(transitionClauses, false, false));
            f = and(f, neg(listToFormula(safetyClauses, false, true)));

            /*
            If (Fk /\ T /\ ¬P') is satisfiable the invariant doesn't keep the program safe so move to the erroneous
            phase. Otherwise go to the holding phase
             */
            if (invariantHolds(f)) {
                /*
                Erroneous Phase

                Remove the counter example produced by the SAT-Solver
                 */
                System.out.println("Go to Erroneous Phase\n");

                System.out.println("Counter Example:" + counterClause);

                boolean isSCCorrect = erroneousPhase(counter);

                if (!isSCCorrect){
                    break;
                }
            } else {
                //As (Fk /\ T /\ ¬P') holds, create a new invariant via the holding phase
                System.out.println("Go to Holding Phase\n");

                //Set the old invariant to equal the new one
                invariantOld = invariantNew;

                //New invariant constructed via the holding phase
                invariantClauses = (holdingPhase(invariantClauses));
                //New invariant constructed to include the counter example
                invariantNew = listToFormula(invariantClauses, false, false);
                //Save the new invariant in the ArrayList of invariants

                if (counter > invariants.size()-2) {
                    Invariant newFk = new Invariant(invariantNew);
                    invariants.add(newFk);
                    System.out.println("Invariant created");
                } else {
                    invariants.get(counter+1).setInvariant(invariantNew);
                    System.out.println("Invariant updated");
                }

                System.out.println("F" + (counter + 2));
                saveInvariant(invariantClauses, ("f" + (counter + 2)));
                System.out.println("Invariant clauses written: " + invariantClauses);

                //Increment the counter
                counter++;
            }

            if (counter > 0) {
                System.out.println("\nOld: " + invariants.get(counter - 1).getInvariant());
            }
            System.out.println("New: " + invariants.get(counter).getInvariant());

            //¬((new ∨ ¬old) ∧ (old ∨ ¬new))
            /*If the new invariant is syntactically equivalent then the iteration phase can stop as the new and old
            invariants are the same. Otherwise continue with another iteration
             */
            if (counter > 0) {
                Formula invariantCheck = neg(and(or(invariants.get(counter).getInvariant(), neg(invariants.get(counter - 1).getInvariant())), or(invariants.get(counter - 1).getInvariant(), neg(invariants.get(counter).getInvariant()))));
                if (isSatisfiable(invariantCheck)) {
                    System.out.println("\nFk != Fk+1");
                    invariantsEqual = false;
                } else {
                    System.out.println("\nFk = Fk+1");
                    invariantsEqual = true;
                }
            } else {
                invariantsEqual = false;
            }

//            //Old
//            //If the old and new invariants are the same then set the boolean value to true to end the iteration phase
//            if (invariants.get(counter).toString().equals(invariants.get(counter - 1).toString())) {
//                System.out.println("True");
//                invariantsEqual = true;
//            } else {
//                System.out.println("False");
//                invariantsEqual = false;
//            }

            //Loop continues while old and new invariants aren't equal
        } while (!invariantsEqual);
        System.out.println("Done");
        //Save and output the final invariant
        outputInvariant(invariantClauses);

        System.out.println();
        //Output all invariants created for testing purposes
        for (int i = 0; i < invariants.size(); i++) {
            System.out.println("F" + (i + 1) + ": " + invariants.get(i).getInvariant());
        }
    }

    /**
     * Output the final invariant and save it to a .cnf file in Dimacs format
     *
     * @param invariant List invariant as a list of integers
     */
    private static void outputInvariant(List<List<Integer>> invariant) {
        try {
            //Creates a new instance of filewriter
            FileWriter fileWriter = new FileWriter(path + "invariant.cnf");

            System.out.println("\nInvariant:");

            //Counter for the number of clauses in the invariant
            int clauses = 0;

            //String to store the elements in the Dimacs format to be written to the file
            String dimacs = "";

            //Loops through each element in the invariant's clauses, adding each to the string to be written to the file
            for (int i = 0; i < invariant.size(); i++) {
                for (int j = 0; j < invariant.get(i).size(); j++) {
                    System.out.print(invariant.get(i).get(j) + " ");
                    dimacs += invariant.get(i).get(j) + " ";
                }
                //Increment the number of clauses, and create a new line with the 0 to signify the logical and
                clauses++;
                System.out.print("0\n");
                dimacs += "0\n";
            }

            //Write to the file
            fileWriter.write("c invariant.cnf \nc\np cnf " + numberOfVars + " " + clauses + "\n");
            fileWriter.write(dimacs);
            fileWriter.close(); //Closes the fileWriter

        } catch (FileNotFoundException e) { // If the file does not exist, handles problem.
            System.err.println("File users.txt does not exist.");
            System.exit(-1);
        } catch (IOException e) { // If there was a problem writing, gives feedback .
            System.err.println("Caught IO error, writing to users.txt");
            System.exit(-1);
        }
    }

    /**
     * Output the final invariant and save it to a .cnf file in Dimacs format
     *
     * @param invariant List invariant as a list of integers
     */
    private static void saveInvariant(List<List<Integer>> invariant, String filename) {
        try {
            //Creates a new instance of filewriter
            FileWriter fileWriter = new FileWriter(path + filename + ".cnf");

            //Counter for the number of clauses in the invariant
            int clauses = 0;

            //String to store the elements in the Dimacs format to be written to the file
            String dimacs = "";

            //Loops through each element in the invariant's clauses, adding each to the string to be written to the file
            for (int i = 0; i < invariant.size(); i++) {
                for (int j = 0; j < invariant.get(i).size(); j++) {
                    dimacs += invariant.get(i).get(j) + " ";
                }
                //Increment the number of clauses, and create a new line with the 0 to signify the logical and
                clauses++;
                dimacs += "0\n";
            }

            //Write to the file
            fileWriter.write("c " + filename + ".cnf \nc\np cnf " + numberOfVars + " " + clauses + "\n");
            fileWriter.write(dimacs);
            fileWriter.close(); //Closes the fileWriter

        } catch (FileNotFoundException e) { // If the file does not exist, handles problem.
            System.err.println("File users.txt does not exist.");
            System.exit(-1);
        } catch (IOException e) { // If there was a problem writing, gives feedback.
            System.err.println("Caught IO error, writing to users.txt");
            System.exit(-1);
        }
    }

    private static void saveCounterExample(List<Integer> counterClause) {
        try {
            //Creates a new instance of filewriter
            FileWriter fileWriter = new FileWriter(path + "counterExamples.cnf", true);

            //String to store the elements in the Dimacs format to be written to the file
            String dimacs = "";

            //Loops through each element in the counter example's clauses, adding each to the string to be written to the file
            for (int i = 0; i < counterClause.size(); i++) {
                dimacs += counterClause.get(i) + " ";
            }
            dimacs += "0\n";

            //Write to the file
            fileWriter.write("Counter Example: " + dimacs);
            fileWriter.close(); //Closes the fileWriter

        } catch (FileNotFoundException e) { // If the file does not exist, handles problem.
            System.err.println("File users.txt does not exist.");
            System.exit(-1);
        } catch (IOException e) { // If there was a problem writing, gives feedback.
            System.err.println("Caught IO error, writing to users.txt");
            System.exit(-1);
        }
    }

    private static boolean erroneousPhase(int counter) throws TimeoutException, IOException {
        /*Check if the the first the counter example holds with the first invariant via F1 /\ ¬s /\ T => ¬s'
                If this holds continue, otherwise there is a fault in the safety property
                 */
        Formula counterCheck = invariants.get(0).getInvariant();
        counterCheck = and(counterCheck, neg(counterExample));
        counterCheck = and(counterCheck, listToFormula(transitionClauses, false, false));
        counterCheck = and(counterCheck, (counterExamplePrimed));

        /* If ¬(F1 /\ ¬s /\ T => ¬s) is unsatisfiable the safety property is fine so continue, otherwise break and
        output that it is incorrect
        */
        //if (isSatisfiable(neg(counterCheck))) {
        if (!isSatisfiable(counterCheck)) {

            System.out.println("sat");

            System.out.println(getClause(0,1));

            //Variable to count the latest invariant that ¬s holds in
            int l = 0;

            //Variable to store if ¬s holds for an invariant
            boolean isUnsat = false;

            //Save the counter examples produced, file needs wiping before use
            //saveCounterExample(counterClause);

            /* For each invariant, check if ¬s holds under it. If so add ¬s to the invariant to update it. Each
            time incrementing l by 1. This continues until either ¬s is not satisiable (Fk /\ ¬s /\ T => not s'
            is unsatisfiable) or l is greater than the total number of invariants
             */
            do {
                //Invariant at position l
                invariants.get(l).setInvariant(and(invariants.get(l).getInvariant(), neg(counterExample)));
                System.out.println("\n F" + (l + 1) + ": "  + invariants.get(l).getInvariant() + "\n");

                        /*Check if ¬(Fk /\ ¬s /\ T => ¬s') is satisfiable, if so add it to the invariant and continue
                        to the next invariant providing there is another invariant left to check. If it is unsatisfiable
                        then
                         */
                counterCheck = invariants.get(l).getInvariant();
                counterCheck = and(counterCheck, neg(counterExample));
                counterCheck = and(counterCheck, listToFormula(transitionClauses, false, false));
                counterCheck = and(counterCheck, (counterExamplePrimed));

                if (!isSatisfiable(counterCheck)) {
                    //Update the new invariant
                    isUnsat = true;
                    invariantClauses = readCNF(path + "F" + (l + 1) + ".cnf");
                    invariantClauses.add(counterClause);
                    invariants.get(l).setInvariant(listToFormula(invariantClauses, false, false));
                    saveInvariant(invariantClauses, "F" + (l + 1));

                    //Set counter to be at this invariant
                    counter = l;
                } else {
                    isUnsat = false;
                }

                //Increment l to check the next invariant
                l++;
            } while (isUnsat && (l < invariants.size()));

            System.out.println("Invariant clauses: " + invariantClauses);

            //Set the old invariant to equal the new one
            invariantOld = invariantNew;
            //New invariant constructed to include the counter example
            invariantNew = listToFormula(invariantClauses, false, false);

            return true;
        } else {
            //Finish the iteration phase as the safety property is incorrect
            System.out.println("Safety does not hold\n");
            return false;
        }
    }

    private static Formula getClause(int counter, int length){
        String clause = "";
        for (int i = counter; i < length; i++) {
            clause += counterClause.get(i) + " ";
        }
        return clauseToFormula(counterClause.subList(counter, length),false,false);
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
}