package utils;

import formula.ltlf.*;
import net.sf.tweety.logics.pl.syntax.Proposition;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * @author Mathias Hedqvist 2022-06-03
 */
public class RandomFormulaGenerator {
    private Random random;

    public RandomFormulaGenerator() {
        this(new Random());
    }

    public RandomFormulaGenerator(Random random) {
        this.random = random;
    }

    public LTLfFormula getRandomFormula(List<Proposition> props, int length, double probabilityUorR) {
        if (length < 1) {
            throw new IllegalArgumentException("Formula length must be more than 0");
        } else if (probabilityUorR < 0 || probabilityUorR > 1) {
            throw new IllegalArgumentException("Illegal probability value " + probabilityUorR);
        } else if (props.isEmpty()) {
            throw new IllegalArgumentException("Proposition list was empty");
        }

        LTLfFormula formula;
        LTLfFormula left;
        LTLfFormula right;

        /* base case when length is 1 or 2 */
        if (length == 1) {
            return getUnitLengthFormula(props);
        } else if (length == 2) {
            return getLength2Formula(props);
        }

        /* calc probability for operators */
        double probTemp = probabilityUorR / 2; // U, R
        double probNotTemp = (1 - probabilityUorR) / 4; // !, X, &&, ||
        double randomOp = random.nextDouble();

        /* calc possible size for binary formulas */
        int possSize = length - 2;
        int s1 = random.nextInt(possSize) + 1;
        int s2 = length - s1 - 1;

        if (randomOp < probTemp) {
            // until
            left = getRandomFormula(props, s1, probabilityUorR);
            right = getRandomFormula(props, s2, probabilityUorR);
            formula = new LTLfUntilFormula(left, right);
        } else if (randomOp < (2 * probTemp)) {
            // release
            left = getRandomFormula(props, s1, probabilityUorR);
            right = getRandomFormula(props, s2, probabilityUorR);
            formula = new LTLfReleaseFormula(left, right);
        } else if (randomOp < (2 * probTemp + 1 * probNotTemp)) {
            // not
            formula = new LTLfTempNotFormula(getRandomFormula(props, length - 1, probabilityUorR));
        } else if (randomOp < (2 * probTemp + 2 * probNotTemp)) {
            // next
            formula = new LTLfNextFormula(getRandomFormula(props, length - 1, probabilityUorR));
        } else if (randomOp < (2 * probTemp + 3 * probNotTemp)) {
            // and
            left = getRandomFormula(props, s1, probabilityUorR);
            right = getRandomFormula(props, s2, probabilityUorR);
            formula = new LTLfTempAndFormula(left, right);
        } else {
            // or
            left = getRandomFormula(props, s1, probabilityUorR);
            right = getRandomFormula(props, s2, probabilityUorR);
            formula = new LTLfTempOrFormula(left, right);
        }

        return formula;
    }

    public LTLfFormula getRandomFormulaForG(List<Proposition> props, int length, double probabilityUorR) {
        if (length < 1) {
            throw new IllegalArgumentException("Formula length must be more than 0");
        } else if (probabilityUorR < 0 || probabilityUorR > 1) {
            throw new IllegalArgumentException("Illegal probability value " + probabilityUorR);
        } else if (props.isEmpty()) {
            throw new IllegalArgumentException("Proposition list was empty");
        }

        LTLfFormula formula;
        LTLfFormula left;
        LTLfFormula right;

        /* base case when length is 1 or 2 */
        if (length == 1) {
            return getUnitLengthFormula(props);
        } else if (length == 2) {
            return getLength2Formula(props);
        }

        /* calc probability for operators */
        double probTemp = probabilityUorR / 2; // F, G
        double probNotTemp = (1 - probabilityUorR) / 4; // !, X, &&, ||
        double randomOp = random.nextDouble();

        /* calc possible size for binary formulas */
        int possSize = length - 2;
        int s1 = random.nextInt(possSize) + 1;
        int s2 = length - s1 - 1;

        if (randomOp < probTemp) {
            // finally
            formula = new LTLfEventuallyFormula(getRandomFormulaForG(props, length - 1, probabilityUorR));
        } else if (randomOp < (2 * probTemp)) {
            // globally
            formula = new LTLfGloballyFormula(getRandomFormulaForG(props, length - 1, probabilityUorR));
        } else if (randomOp < (2 * probTemp + 1 * probNotTemp)) {
            // not
            formula = new LTLfTempNotFormula(getRandomFormulaForG(props, length - 1, probabilityUorR));
        } else if (randomOp < (2 * probTemp + 2 * probNotTemp)) {
            // next
            formula = new LTLfNextFormula(getRandomFormulaForG(props, length - 1, probabilityUorR));
        } else if (randomOp < (2 * probTemp + 3 * probNotTemp)) {
            // and
            left = getRandomFormulaForG(props, s1, probabilityUorR);
            right = getRandomFormulaForG(props, s2, probabilityUorR);
            formula = new LTLfTempAndFormula(left, right);
        } else {
            // or
            left = getRandomFormulaForG(props, s1, probabilityUorR);
            right = getRandomFormulaForG(props, s2, probabilityUorR);
            formula = new LTLfTempOrFormula(left, right);
        }

        return formula;
    }

    public static List<Proposition> createPropositionList(int n) {
        if (n > 26) {
            throw new IllegalArgumentException("Number of propositions more than a-z, weird things might happen!");
        }

        List<Proposition> propositions = new ArrayList<>();

        for (int i = 0; i < n; i++) {
            char c = (char) ('a' + i);
            Proposition p = new Proposition(String.valueOf(c));
            propositions.add(p);
        }

        return propositions;
    }

    private LTLfFormula getUnitLengthFormula(List<Proposition> props) {
        int randomIndex = random.nextInt(props.size());
        Proposition p = props.get(randomIndex);
        LTLfFormula formula = new LTLfLocalVar(p);
        return formula;
    }

    private LTLfFormula getLength2Formula(List<Proposition> props) {
        LTLfFormula formula;

        int randomOp = random.nextInt(2);
        if (randomOp == 0) {
            // not
            formula = new LTLfLocalNotFormula(getUnitLengthFormula(props));
        } else {
            // next
            formula = new LTLfNextFormula(getUnitLengthFormula(props));
        }

        return formula;
    }

}
