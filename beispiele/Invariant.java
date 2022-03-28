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

/**
 * Invariant.java
 *
 * @author Harry Bryant
 * <p> Copyright: No copyright </p>
 * <p> Version History:
 * Version 1: Basic constructor and getter method,
 * Version 2: setInvariant method added
 * Version 2.1: Comments </p>
 * <p>
 * Invariant.java stores a formula converted from a list of list of integers. This formula can be returned or
 * overwritten when required
 * </p>
 * @version 3.1
 * <p> Creation Date: 17/03/21 </p>
 * <p> Last Modification Date: 25/03/21 </p>
 */
public class Invariant {

  //Instance of formula to store the invariant
  private Formula invariant;

  /**
   * Constructor, creates the new instance of an invriant and stores the invariant passed as a parameter
   * @param invariant
   */
  public Invariant(Formula invariant) {
    //Store the invariant formula passed as a parameter
    this.invariant = invariant;
  }

  /**
   * Returns the invariant formula
   * @return the formula is returned
   */
  public Formula getInvariant() {
    return invariant;
  }

  /**
   * Update the formula that is currently stored to the one passed as a parameter
   * @param invariant The new invariant formula
   */
  public void setInvariant(Formula invariant) {
    this.invariant = invariant;
  }

  /**
   * Returns the invariant formula as a string
   * @return String with the classes information
   */
  @java.lang.Override
  public java.lang.String toString() {
    return "Invariant{" +
            "invariant=" + invariant +
            '}';
  }
}