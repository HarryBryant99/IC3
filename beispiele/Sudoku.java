package beispiele;

import cnf.Formula;
import cnf.VarName;
import static cnf.CNF.*;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import org.sat4j.specs.TimeoutException;

public class Sudoku {

  TreeMap<Integer, Map<Integer, Map<Integer, VarName>>> posVars = null;

  private void makeVars() {
    posVars = new TreeMap<Integer, Map<Integer, Map<Integer, VarName>>>();

    reset();

    for (int x = 0; x < 9; x++) {
      Map<Integer, Map<Integer, VarName>> m1 = new TreeMap<Integer, Map<Integer, VarName>>();
      for (int y = 0; y < 9; y++) {
        Map<Integer, VarName> m2 = new TreeMap<Integer, VarName>();
        for (int z = 0; z < 10; z++) {
          m2.put(z, freshVarName());
        }
        m1.put(y, m2);
      }
      posVars.put(x, m1);
    }
  }

  private VarName pos(int x, int y, int z) {
    return posVars.get(x).get(y).get(z);
  }

  private Formula sudoku(Integer[][] givens) {
    // Variablennamen erzeugen
    makeVars();

    List<Formula> conditions = new LinkedList<Formula>();

    // Vorgaben
    for (int x = 0; x < 9; x++) {
      for (int y = 0; y < 9; y++) {
        if (givens[x][y] != null) {
          conditions.add(var(pos(x, y, givens[x][y])));
        }
      }
    }

    // an jeder Stelle eine Zahl
    for (int x = 0; x < 9; x++) {
      for (int y = 0; y < 9; y++) {
        List<Formula> l = new LinkedList<Formula>();
        for (int z = 0; z < 10; z++) {
          l.add(var(pos(x, y, z)));
        }
        conditions.add(or(l));
      }
    }

    // nicht zwei Zahlen an der gleichen Stelle
    for (int x = 0; x < 9; x++) {
      for (int y = 0; y < 9; y++) {
        for (int z1 = 0; z1 < 10; z1++) {
          for (int z2 = z1 + 1; z2 < 10; z2++) {
            conditions.add(or(neg(var(pos(x, y, z1))), neg(var(pos(x, y, z2)))));
          }
        }
      }
    }

    // jede Zahl hoechstens einmal in jeder Spalte
    for (int x = 0; x < 9; x++) {
      for (int y1 = 0; y1 < 9; y1++) {
        for (int y2 = y1 + 1; y2 < 9; y2++) {
          for (int z = 0; z < 10; z++) {
            conditions.add(or(neg(var(pos(x, y1, z))), neg(var(pos(x, y2, z)))));
          }
        }
      }
    }

    // jede Zahl hoechstens einmal in jeder Zeile
    for (int y = 0; y < 9; y++) {
      for (int x1 = 0; x1 < 9; x1++) {
        for (int x2 = x1 + 1; x2 < 9; x2++) {
          for (int z = 0; z < 10; z++) {
            conditions.add(or(neg(var(pos(x1, y, z))), neg(var(pos(x2, y, z)))));
          }
        }
      }
    }

    // keine Zahl in einem 3x3-Block doppelt
    for (int bx = 0; bx < 3; bx++) {
      for (int by = 0; by < 3; by++) {
        for (int x1 = 3 * bx; x1 < 3 * bx + 3; x1++) {
          for (int x2 = x1 + 1; x2 < 3 * bx + 3; x2++) {
            for (int y1 = 3 * by; y1 < 3 * by + 3; y1++) {
              for (int y2 = y1 + 1; y2 < 3 * by + 3; y2++) {
                for (int z = 0; z < 10; z++) {
                  conditions.add(or(neg(var(pos(x1, y1, z))), neg(var(pos(x2, y2, z)))));
                }
              }
            }
          }
        }
      }
    }

    return and(conditions);
  }

  public static void main(String[] args) throws TimeoutException {

    Integer b = null;
    Integer[][] sudoku = {
      new Integer[]{6, b, b, b, 1, 7, 5, b, b},
      new Integer[]{b, 8, 1, 2, b, b, b, 7, b},
      new Integer[]{b, b, b, b, b, 5, b, b, b},
      new Integer[]{b, 2, 9, 4, b, b, b, b, 1},
      new Integer[]{b, 5, 4, b, 2, b, b, 3, b},
      new Integer[]{b, b, 6, b, 7, 8, b, 5, 4},
      new Integer[]{b, b, b, b, b, 9, 3, b, 7},
      new Integer[]{b, b, 3, 8, b, b, 4, b, b},
      new Integer[]{b, b, 5, b, b, b, b, 9, b},};
    Sudoku instance = new Sudoku();

    Formula f = instance.sudoku(sudoku);
    Set<VarName> trueVars = satisfiable(f);
    if (trueVars == null) {
      System.out.println("Nicht erfuellbar.");
    } else {
      // erfuellbar
      for (int x = 0; x < 9; x++) {
        for (int y = 0; y < 9; y++) {
          for (int z = 0; z < 10; z++) {
            if (trueVars.contains(instance.pos(x, y, z))) {
              System.out.print(z + " ");
            }
          }
        }
        System.out.println();
      }
    }
  }
}
