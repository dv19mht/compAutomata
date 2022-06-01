import formula.ldlf.LDLfFormula;
import formula.ltlf.*;
import net.sf.tweety.logics.pl.syntax.Proposition;
import org.junit.Test;

import java.util.*;

/**
 * @author Mathias Hedqvist 2022-06-03
 */
public class RandomFormulaTest {
    Random random = new Random();
    List<Proposition> propList;

    @Test
    public void formBuildingTest() {
        LTLfFormula left = new LTLfLocalVar(new Proposition("a"));
        LTLfFormula right = new LTLfLocalVar(new Proposition("b"));
        LTLfFormula formula = new LTLfTempAndFormula(left, right);
        LDLfFormula ldlfFormula = formula.toLDLf();

        System.out.println(formula);
        System.out.println(ldlfFormula);
    }

    @Test
    public void randomFormulaTest() {
        // N = propositions, L = length of formula, P = probability of generating temp op (U and R)
//        random.setSeed(1);

        propList = createPropositionList(3);
        double prob = (double) 1 / 3;

        for (int i = 3; i < 13; i++) {
            LTLfFormula formula = getRandomFormula(propList, i, prob);
            LDLfFormula ldlfFormula = formula.toLDLf();
            LDLfFormula ldlfFormulaNnf = (LDLfFormula) ldlfFormula.nnf();

            System.out.println("L: " + i);
            System.out.println("LTLf: " + formula);
            System.out.println("LDLf: " + ldlfFormula);
            System.out.println("nnf: " + ldlfFormulaNnf);
        }
    }

    @Test
    public void length2FormulaTest() {
        propList = createPropositionList(2);

        for (int i = 0; i < 10; i++) {
            LTLfFormula formula = getLength2Formula(propList);
            System.out.println(formula);
        }
    }

    @Test
    public void unitLengthFormulaTest() {
        propList = createPropositionList(2);

        for (int i = 0; i < 10; i++) {
            LTLfFormula formula = getUnitLengthFormula(propList);
            System.out.println(formula);
        }
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

    private LTLfFormula getRandomFormula(List<Proposition> props, int length, double probabilityUorR) {
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

    private List<Proposition> createPropositionList(int n) {
        List<Proposition> propositions = new ArrayList<>();

        for (int i = 0; i < n; i++) {
            char c = (char) ('a' + i);
            Proposition p = new Proposition(String.valueOf(c));
            propositions.add(p);
        }

        return propositions;
    }
}
