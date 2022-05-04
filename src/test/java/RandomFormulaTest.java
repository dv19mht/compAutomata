import formula.ltlf.LTLfFormula;
import formula.ltlf.LTLfLocalNotFormula;
import formula.ltlf.LTLfLocalVar;
import formula.ltlf.LTLfNextFormula;
import net.sf.tweety.logics.pl.syntax.Proposition;
import org.junit.Test;

import java.util.*;

public class RandomFormulaTest {
    Random random = new Random();
    List<Proposition> propList;

    @Test
    public void randomFormulaTest() {
        // N = propositions, L = length of formula, P = probability of generating temp op (U and R)

        /* unit-length formula */
        // Choose one variable uniformly between NLP

        /* formula of length 2 */
        // Generate op(p) where op is {!, X} and p is a variable

        /* formula of length 3+ */
        // Choose from {U, R} with probability P/2
        // Choose from {!, X, &&, ||} with probability (1-P)/4
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

    private LTLfFormula getRandomFormula(List<Proposition> props, int length, double probabilityTemp) {
        LTLfFormula formula = null;

        /* base case when length is 1 or 2 */
        if (length == 1) {
            return getUnitLengthFormula(props);
        } else if (length == 2) {
            return getLength2Formula(props);
        }

        double probTemp = probabilityTemp / 2; // U, R
        double probNotTemp = (1 - probabilityTemp) / 4; // !, X, &&, ||
        double randomOp = random.nextDouble();

        if (randomOp < probTemp) {
            // until
        } else if (randomOp < (2 * probTemp)) {
            // release
        } else if (randomOp < (2 * probTemp + 1 * probNotTemp)) {
            // not
        } else if (randomOp < (2 * probTemp + 2 * probNotTemp)) {
            // next
        } else if (randomOp < (2 * probTemp + 3 * probNotTemp)) {
            // and
        } else {
            // or
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
