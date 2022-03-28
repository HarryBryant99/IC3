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

public class ZiegeKohlWolfHirte {

  Map<Integer, Map<Integer, VarName>> linksVars = null;
  Map<Integer, Map<Integer, VarName>> rechtsVars = null;

  final static int kohl = 0;
  final static int ziege = 1;
  final static int wolf = 2;
  final static int hirte = 3;
  final static String namen[] = {"Kohl", "Ziege", "Wolf", "Hirte"};

  private void makeVars(int maxZeit) {
    linksVars = new TreeMap<Integer, Map<Integer, VarName>>();
    rechtsVars = new TreeMap<Integer, Map<Integer, VarName>>();

    reset();

    for (int t = 0; t <= maxZeit; t++) {
      Map<Integer, VarName> m = new TreeMap<Integer, VarName>();
      for (int p = 0; p < 4; p++) {
        m.put(p, freshVarName());
      }
      linksVars.put(t, m);
    }

    for (int t = 0; t <= maxZeit; t++) {
      Map<Integer, VarName> m = new TreeMap<Integer, VarName>();
      for (int p = 0; p < 4; p++) {
        m.put(p, freshVarName());
      }
      rechtsVars.put(t, m);
    }
  }

  private VarName links(int pers, int t) {
    return linksVars.get(t).get(pers);
  }

  private VarName rechts(int pers, int t) {
    return rechtsVars.get(t).get(pers);
  }

  private Formula ziegeWolfKohlHirte(int maxZeit) {
    // Variablennamen erzeugen
    makeVars(maxZeit);

    List<Formula> conditions = new LinkedList<Formula>();

    // Startbedingung
    for (int i = 0; i < 4; i++) {
      conditions.add(var(links(i, 0)));
    }

    // Endbedingung
    for (int i = 0; i < 4; i++) {
      conditions.add(var(rechts(i, maxZeit)));
    }

    // niemand ist sowohl links als auch rechts,
    // jeder ist entweder links oder rechts
    for (int t = 0; t <= maxZeit; t++) {
      for (int i = 0; i < 4; i++) {
        conditions.add(neg(and(var(links(i, t)), var(rechts(i, t)))));
        conditions.add(or(var(links(i, t)), var(rechts(i, t))));
      }
    }

    // niemals Ziege und Kohl ohne Hirte und niemals Wolf und Ziege ohne Hirte
    for (int t = 0; t <= maxZeit; t++) {
      conditions.add(imp(and(var(links(ziege, t)), var(links(kohl, t))), var(links(hirte, t))));
      conditions.add(imp(and(var(rechts(ziege, t)), var(rechts(kohl, t))), var(rechts(hirte, t))));
      conditions.add(imp(and(var(links(ziege, t)), var(links(wolf, t))), var(links(hirte, t))));
      conditions.add(imp(and(var(rechts(ziege, t)), var(rechts(wolf, t))), var(rechts(hirte, t))));
    }

    // Schrittfunktion
    for (int t = 0; t < maxZeit; t++) {

      List<Formula> stept = new LinkedList<Formula>();

      // 1. Moeglichkeit: nichts aendert sich
      List<Formula> l = new LinkedList<Formula>();
      for (int i = 0; i < 4; i++) {
        l.add(iff(var(links(i, t)), var(links(i, t + 1))));
        l.add(iff(var(rechts(i, t)), var(rechts(i, t + 1))));
      }
      stept.add(and(l));

      // 2. Möglichkeit: Der Hirte setzt über den Fluss und nimmt Wolf,
      //                 Ziege oder Kohl mit.
      for (int i = 0; i < 4; i++) {
        l = new LinkedList<Formula>();
        l.add(iff(var(links(i, t)), var(links(hirte, t))));
        l.add(iff(var(rechts(i, t)), var(rechts(hirte, t))));
        l.add(iff(var(links(i, t)), var(rechts(i, t + 1))));
        l.add(iff(var(rechts(i, t)), var(links(i, t + 1))));
        l.add(iff(var(links(hirte, t)), var(rechts(hirte, t + 1))));
        l.add(iff(var(rechts(hirte, t)), var(links(hirte, t + 1))));
        for (int others = 0; others < 4; others++) {
          if (i != others && hirte != others) {
            l.add(iff(var(links(others, t)), var(links(others, t + 1))));
            l.add(iff(var(rechts(others, t)), var(rechts(others, t + 1))));
          }
        }
        stept.add(and(l));
      }

      conditions.add(or(stept));
    }

    return and(conditions);
  }

  public static void main(String[] args) throws TimeoutException {

    int maxZeit = 7;
    ZiegeKohlWolfHirte instance = new ZiegeKohlWolfHirte();

    Formula f = instance.ziegeWolfKohlHirte(maxZeit);
    Set<VarName> trueVars = satisfiable(f);
    if (trueVars == null) {
      System.out.println("Nicht erfuellbar.");
    } else {
      // erfuellbar
      for (int t = 0; t <= maxZeit; t++) {
        System.out.print("Zeit " + t + ": ");
        for (int i = 0; i < 4; i++) {
          if (trueVars.contains(instance.links(i, t))) {
            System.out.print("" + namen[i] + " ");
          }
        }
        System.out.print(" |~~~~~Fluss~~~~~| ");
        for (int i = 0; i < 4; i++) {
          if (trueVars.contains(instance.rechts(i, t))) {
            System.out.print("" + namen[i] + " ");
          }
        }
        System.out.println();
      }
    }
  }
}
