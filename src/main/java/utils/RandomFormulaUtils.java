package utils;

import formula.ltlf.*;
import net.sf.tweety.logics.pl.syntax.Proposition;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class RandomFormulaUtils {

    public static LTLfFormula getRandomFormula(List<Proposition> props, int length, double probabilityUorR) {
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
        Random random = new Random();


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

    public static LTLfFormula getRandomFormulaNoUorR(List<Proposition> props, int length, double probabilityUorR) {
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
        Random random = new Random();

        /* base case when length is 1 or 2 */
        if (length == 1) {
            return getUnitLengthFormula(props);
        } else if (length == 2) {
            return getLength2Formula(props);
        }

        int randInt = random.nextInt(4);

        /* calc possible size for binary formulas */
        int possSize = length - 2;
        int s1 = random.nextInt(possSize) + 1;
        int s2 = length - s1 - 1;

        if (randInt == 0) {
            // not
            formula = new LTLfTempNotFormula(getRandomFormulaNoUorR(props, length - 1, probabilityUorR));
        } else if (randInt == 1) {
            // next
            formula = new LTLfNextFormula(getRandomFormulaNoUorR(props, length - 1, probabilityUorR));
        } else if (randInt == 2) {
            // and
            left = getRandomFormulaNoUorR(props, s1, probabilityUorR);
            right = getRandomFormulaNoUorR(props, s2, probabilityUorR);
            formula = new LTLfTempAndFormula(left, right);
        } else {
            // or
            left = getRandomFormulaNoUorR(props, s1, probabilityUorR);
            right = getRandomFormulaNoUorR(props, s2, probabilityUorR);
            formula = new LTLfTempOrFormula(left, right);
        }

        return formula;
    }

    public static LTLfFormula getRandomFormulaForG(List<Proposition> props, int length, double probabilityUorR, int seed) {
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
        Random random = new Random();
        random.setSeed(seed);

        /* base case when length is 1 or 2 */
        if (length == 1) {
            return getUnitLengthFormula(props, seed);
        } else if (length == 2) {
            return getLength2Formula(props, seed);
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
            formula = new LTLfEventuallyFormula(getRandomFormulaForG(props, length - 1, probabilityUorR, seed));
        } else if (randomOp < (2 * probTemp)) {
            // globally
            formula = new LTLfGloballyFormula(getRandomFormulaForG(props, length - 1, probabilityUorR, seed));
        } else if (randomOp < (2 * probTemp + 1 * probNotTemp)) {
            // not
            formula = new LTLfTempNotFormula(getRandomFormulaForG(props, length - 1, probabilityUorR, seed));
        } else if (randomOp < (2 * probTemp + 2 * probNotTemp)) {
            // next
            formula = new LTLfNextFormula(getRandomFormulaForG(props, length - 1, probabilityUorR, seed));
        } else if (randomOp < (2 * probTemp + 3 * probNotTemp)) {
            // and
            left = getRandomFormulaForG(props, s1, probabilityUorR, seed);
            right = getRandomFormulaForG(props, s2, probabilityUorR, seed);
            formula = new LTLfTempAndFormula(left, right);
        } else {
            // or
            left = getRandomFormulaForG(props, s1, probabilityUorR, seed);
            right = getRandomFormulaForG(props, s2, probabilityUorR, seed);
            formula = new LTLfTempOrFormula(left, right);
        }

        return formula;
    }

    public static List<Proposition> createPropositionList(int n) {
        List<Proposition> propositions = new ArrayList<>();

        for (int i = 0; i < n; i++) {
            char c = (char) ('a' + i);
            Proposition p = new Proposition(String.valueOf(c));
            propositions.add(p);
        }

        return propositions;
    }

    private static LTLfFormula getUnitLengthFormula(List<Proposition> props) {
        return getUnitLengthFormula(props, 0);
    }

    private static LTLfFormula getUnitLengthFormula(List<Proposition> props, int seed) {
        Random random = new Random();
        if (seed != 0) {
            random.setSeed(seed);
        }

        int randomIndex = random.nextInt(props.size());
        Proposition p = props.get(randomIndex);
        LTLfFormula formula = new LTLfLocalVar(p);
        return formula;
    }

    private static LTLfFormula getLength2Formula(List<Proposition> props) {
        return getLength2Formula(props, 0);
    }

    private static LTLfFormula getLength2Formula(List<Proposition> props, int seed) {
        LTLfFormula formula;
        Random random = new Random();
        if (seed != 0) {
            random.setSeed(seed);
        }

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
