Sample programs:
   javac -cp.: org.sat4j.core.jar examples / Test.java
   java -cp.: org.sat4j.core.jar examples / test
 
   javac -cp.: org.sat4j.core.jar examples / Sudoku.java
   java -cp.: org.sat4j.core.jar examples / Sudoku
 
   javac -cp.: org.sat4j.core.jar examples / ZiegeKohlWolfHirte.java
   java -cp.: org.sat4j.core.jar examples / ZiegeKohlWolfHirte

The SAT4J satellite solver is used for the tests for satisfiability.
This is contained in the file org.sat4j.core.jar, which is used for the
Compilation and execution must be in the CLASSPATH.

Like ZCHAFF, SAT4J can also be used as an independent satellite solver
that receives its input as a text file in DIMACS format.
Then call:
   java -jar org.sat4j.core.jar formula.dimacs