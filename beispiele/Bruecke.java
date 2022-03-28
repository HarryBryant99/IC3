package beispiele;

import cnf.Formula;
import cnf.VarName;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import static cnf.CNF.*;
import org.sat4j.specs.TimeoutException;

public class Bruecke {

  static Integer zeiten[] = {1, 2, 5, 8};
  static int maxZeit = 15;
  //
  static int lampe = zeiten.length;

  /* Die Variablen haben folgende Bedeutung:
	* links(i, t) -- Person i ist zum Zeitpunkt t auf der linken Seite
	* rechts(i, t) -- Person i ist zum Zeitpunkt t auf der rechten Seite
	* brueckeNachLinks(i, t) -- Person i ist zum Zeitpunkt t auf der Bruecke und geht nach links
	* brueckeNachRechts(i, t) -- Person i ist zum Zeitpunkt t auf der Bruecke und geht nach rechts
	* restDauer(r, t) -- Eine Ueberquerung ist im Gange und dauert noch r Minuten.
	*
	* Die Lampe wird als "Person" mit Index i=lampe betrachtet.
	*/
  static VarName[][] linksVars = null;
  static VarName[][] rechtsVars = null;
  static VarName[][] brueckeNachLinksVars = null;
  static VarName[][] brueckeNachRechtsVars = null;
  static VarName[][] restDauerVars = null;

  static Formula links(int pers, int t) {
    return var(linksVars[t][pers]);
  }

  static Formula rechts(int pers, int t) {
    return var(rechtsVars[t][pers]);
  }

  static Formula brueckeNachLinks(int pers, int t) {
    return var(brueckeNachLinksVars[t][pers]);
  }

  static Formula brueckeNachRechts(int pers, int t) {
    return var(brueckeNachRechtsVars[t][pers]);
  }

  static Formula restDauer(int rest, int t) {
    return var(restDauerVars[t][rest]);
  }

  // Eine Formel, die ausdrueckt, dass die Bruecke zum Zeitpunkt t leer ist.
  static Formula brueckeLeer(int t) {
    int n = zeiten.length;
    List<Formula> l = new LinkedList<Formula>();
    for (int pers = 0; pers < n; pers++) {
      l.add(neg(brueckeNachLinks(pers, t)));
      l.add(neg(brueckeNachRechts(pers, t)));
    }
    return and(l);
  }

  // Die Formel fuer das Brueckenproblem
  static Formula brueckenUeberquerung() {
    int n = zeiten.length;
    int maxDauer = 0;

    for (Integer dauer : zeiten) {
      maxDauer = Math.max(maxDauer, dauer);
    }

    // Variablennamen erzeugen
    makeVars(n, maxDauer, maxZeit);

    List<Formula> conditions = new LinkedList<Formula>();

    // Startbedingung
    for (int i = 0; i <= n; i++) { // Personen und Lampe
      conditions.add(links(i, 0));
    }

    // Endbedingung
    for (int i = 0; i < n; i++) { // nur Personen
      conditions.add(rechts(i, maxZeit));
    }

    // Jede Person sowie die Lampe ist an genau einer Stelle.
    for (int t = 0; t <= maxZeit; t++) {
      for (int i = 0; i <= n; i++) { // Personen und Lampe
        conditions.add(imp(links(i, t), and(neg(rechts(i, t)), and(neg(brueckeNachLinks(i, t)), neg(brueckeNachRechts(i, t))))));
        conditions.add(imp(rechts(i, t), and(neg(links(i, t)), and(neg(brueckeNachLinks(i, t)), neg(brueckeNachRechts(i, t))))));
        conditions.add(imp(brueckeNachLinks(i, t), and(neg(links(i, t)), and(neg(rechts(i, t)), neg(brueckeNachRechts(i, t))))));
        conditions.add(imp(brueckeNachRechts(i, t), and(neg(links(i, t)), and(neg(rechts(i, t)), neg(brueckeNachLinks(i, t))))));
        conditions.add(or(links(i, t), or(rechts(i, t), or(brueckeNachRechts(i, t), brueckeNachLinks(i, t)))));
      }
    }

    // Die Restdauer einer Ueberquerung ist eine eindeutige Zahl, d.h.
    // zwei verschiedene Restzeiten koennen nicht gleichzeitig wahr sein.
    for (int t = 0; t <= maxZeit; t++) {
      for (int rest1 = 0; rest1 < maxDauer; rest1++) {
        for (int rest2 = rest1 + 1; rest2 < maxDauer; rest2++) {
          conditions.add(neg(and(restDauer(rest1, t), restDauer(rest2, t))));
        }
      }
    }

    // Die Restdauer einer Ueberquerung kann nur dann positiv sein, wenn auch
    // wirklich jemand auf der Bruecke ist.
    for (int t = 0; t <= maxZeit; t++) {
      for (int rest = 1; rest < maxDauer; rest++) {
        conditions.add(imp(restDauer(rest, t), neg(brueckeLeer(t))));
      }
    }

    // Uebergangsrelation
    for (int t = 0; t < maxZeit; t++) {

      List<Formula> possibilities = new LinkedList<Formula>();

      // 1. Moeglichkeit:
      // Keiner ist auf der Bruecke und es aendert sich nichts.
      List<Formula> l = new LinkedList<Formula>();
      l.add(brueckeLeer(t));
      for (int i = 0; i <= n; i++) { // Personen und Lampe
        l.add(iff(links(i, t), links(i, t + 1)));
        l.add(iff(rechts(i, t), rechts(i, t + 1)));
      }
      possibilities.add(and(l));

      // 2. Moeglichkeit: 
      // Eine Ueberquerung ist bereits begonnen und wird nun fortgesetzt.
      l = new LinkedList<Formula>();
      // 2.1. Die Ueberquerung ist noch nicht abgeschlossen, d.h. es gibt
      // jemanden auf der Bruecke.
      l.add(neg(brueckeLeer(t)));
      // 2.2. Positionen aendern sich nur im letzten Schritt der Ueberquerung,
      // bleiben sonst gleich.
      for (int i = 0; i <= n; i++) { // Personen und Lampe
        l.add(imp(links(i, t), links(i, t + 1)));
        l.add(imp(rechts(i, t), rechts(i, t + 1)));
        l.add(imp(restDauer(1, t), imp(brueckeNachLinks(i, t), links(i, t + 1))));
        l.add(imp(restDauer(1, t), imp(brueckeNachRechts(i, t), rechts(i, t + 1))));
        l.add(imp(neg(restDauer(1, t)), iff(brueckeNachLinks(i, t), brueckeNachLinks(i, t + 1))));
        l.add(imp(neg(restDauer(1, t)), iff(brueckeNachRechts(i, t), brueckeNachRechts(i, t + 1))));
      }
      // 2.3. Die restliche fuer die Ueberquerung benoetigte Zeit nimmt ab
      for (int rest = 1; rest < maxDauer; rest++) {
        l.add(imp(restDauer(rest, t), restDauer(rest - 1, t + 1)));
      }
      possibilities.add(and(l));

      // 3. Möglichkeit:
      // Eine neue Ueberquerung wird begonnen
      for (int i = 0; i < n; i++) { // nur Personen
        for (int j = i; j < n; j++) { // nur Personen
          // Beachte: i und j koennen gleich sein, also erfasst dieser
          // Fall sowohl die Ueberquerung durch eine Person als auch durch zwei
          // Personen.
          int dauer = Math.max(zeiten[i], zeiten[j]);
          l = new LinkedList<Formula>();
          // Eine Ueberquerung darf nur angefangen werden, wenn die Bruecke leer ist.
          l.add(brueckeLeer(t));
          // Ueberquerung nur mit Lampe.
          l.add(imp(links(i, t), links(lampe, t)));
          l.add(imp(rechts(i, t), rechts(lampe, t)));
          l.add(imp(links(j, t), links(lampe, t)));
          l.add(imp(rechts(j, t), rechts(lampe, t)));
          // Bei dauer == 1 sind i und j gleich im naechsten
          // Schritt da, sonst sind sie dann auf der Bruecke.
          if (dauer == 1) {
            l.add(imp(links(lampe, t), rechts(lampe, t + 1)));
            l.add(imp(rechts(lampe, t), links(lampe, t + 1)));
            l.add(imp(links(i, t), rechts(i, t + 1)));
            l.add(imp(rechts(i, t), links(i, t + 1)));
            l.add(imp(links(j, t), rechts(j, t + 1)));
            l.add(imp(rechts(j, t), links(j, t + 1)));
          } else {
            l.add(imp(links(lampe, t), brueckeNachRechts(lampe, t + 1)));
            l.add(imp(rechts(lampe, t), brueckeNachLinks(lampe, t + 1)));
            l.add(imp(links(i, t), brueckeNachRechts(i, t + 1)));
            l.add(imp(rechts(i, t), brueckeNachLinks(i, t + 1)));
            l.add(imp(links(j, t), brueckeNachRechts(j, t + 1)));
            l.add(imp(rechts(j, t), brueckeNachLinks(j, t + 1)));
          }
          // Alle anderen bewegen sich nicht.
          for (int otherpers = 0; otherpers < n; otherpers++) { // nur Personen 
            if (i != otherpers && j != otherpers) {
              l.add(imp(links(otherpers, t), links(otherpers, t + 1)));
              l.add(imp(rechts(otherpers, t), rechts(otherpers, t + 1)));
            }
          }
          // Die Ueberquerung dauert nun noch (dauer - 1) Schritte.
          l.add(restDauer(dauer - 1, t + 1));
          possibilities.add(and(l));
        }
      }
      conditions.add(or(possibilities));
    }

    return and(conditions);
  }

  static void makeVars(int n, int maxDauer, int maxZeit) {
    linksVars = new VarName[maxZeit + 1][n + 1];
    rechtsVars = new VarName[maxZeit + 1][n + 1];
    brueckeNachLinksVars = new VarName[maxZeit + 1][n + 1];
    brueckeNachRechtsVars = new VarName[maxZeit + 1][n + 1];
    restDauerVars = new VarName[maxZeit + 1][maxZeit];
    for (int t = 0; t <= maxZeit; t++) {
      for (int p = 0; p <= n; p++) {
        linksVars[t][p] = freshVarName();
        rechtsVars[t][p] = freshVarName();
        brueckeNachLinksVars[t][p] = freshVarName();
        brueckeNachRechtsVars[t][p] = freshVarName();
      }
      for (int d = 0; d < maxDauer; d++) {
        restDauerVars[t][d] = freshVarName();
      }
    }

  }

  public static void main(String[] args) throws TimeoutException {

    Formula f = brueckenUeberquerung();
    Set<VarName> trueVars = satisfiable(f);
    if (trueVars == null) {
      System.out.println("Nicht erfuellbar.");
    } else {
      for (int t = 0; t <= maxZeit; t++) {
        System.out.print("Zeit " + t + ": ");
        for (int pers = 0; pers <= zeiten.length; pers++) {
          if (trueVars.contains(linksVars[t][pers])) {
            System.out.print("" + (pers < zeiten.length ? zeiten[pers] : "L") + " ");
          }
        }
        System.out.print("|-- ");
        for (int pers = 0; pers <= zeiten.length; pers++) {
          if (trueVars.contains(brueckeNachLinksVars[t][pers])) {
            System.out.print("<" + (pers < zeiten.length ? zeiten[pers] : "L") + " ");
          }
          if (trueVars.contains(brueckeNachRechtsVars[t][pers])) {
            System.out.print(">" + (pers < zeiten.length ? zeiten[pers] : "L") + " ");
          }
        }
        System.out.print("--|");
        for (int pers = 0; pers <= zeiten.length; pers++) {
          if (trueVars.contains(rechtsVars[t][pers])) {
            System.out.print("" + (pers < zeiten.length ? zeiten[pers] : "L") + " ");
          }
        }
        for (int restDauer = 1; restDauer < maxZeit; restDauer++) {
          if (trueVars.contains(restDauerVars[t][restDauer])) {
            System.out.print(" (noch " + restDauer + " Min. bis Ankunft)");
          }
        }
        System.out.println();
      }
    }
  }
}
