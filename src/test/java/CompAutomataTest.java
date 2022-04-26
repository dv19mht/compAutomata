import formula.ldlf.LDLfFormula;
import formula.ltlf.LTLfFormula;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import org.junit.Test;
import rationals.Automaton;
import rationals.properties.ModelCheck;
import rationals.transformations.Reducer;
import utils.AutomatonUtils;
import utils.CompAutomatonUtils;
import utils.ParserUtils;

public class CompAutomataTest {

    @Test
    public void compLDLToAutomataTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        compareAutomataOnLDL("tt", declare, ps);

        compareAutomataOnLDL("ff", declare, ps);

        compareAutomataOnLDL("!(tt)", declare, ps);

        compareAutomataOnLDL("!(ff)", declare, ps);

        //diamond formulae
        compareAutomataOnLDL("<true>(tt)", declare, ps);

        compareAutomataOnLDL("<true>(ff)", declare, ps);

        compareAutomataOnLDL("<false>(tt)", declare, ps);

        compareAutomataOnLDL("<false>(ff)", declare, ps);

        compareAutomataOnLDL("<a>(tt)", declare, ps);

        compareAutomataOnLDL("<a>(ff)", declare, ps);

        //box formulae
        compareAutomataOnLDL("[true](tt)", declare, ps);

        compareAutomataOnLDL("[true](ff)", declare, ps); // end

        compareAutomataOnLDL("[false](tt)", declare, ps);

        compareAutomataOnLDL("[false](ff)", declare, ps);

        compareAutomataOnLDL("[a](tt)", declare, ps);

        compareAutomataOnLDL("[a](ff)", declare, ps);

        compareAutomataOnLDL("[!(a)](tt)", declare, ps);

        compareAutomataOnLDL("[!(a)](ff)", declare, ps);

        //star diamond formulae
        compareAutomataOnLDL("<(true)*>(tt)", declare, ps);

        compareAutomataOnLDL("<(true)*>(ff)", declare, ps);

        compareAutomataOnLDL("<(false)*>(tt)", declare, ps);

        compareAutomataOnLDL("<(false)*>(ff)", declare, ps);

        compareAutomataOnLDL("<(a)*>(tt)", declare, ps);

        compareAutomataOnLDL("<(a)*>(ff)", declare, ps);

        //star box formulae
        compareAutomataOnLDL("[(true)*](tt)", declare, ps);

        compareAutomataOnLDL("[(true)*](ff)", declare, ps);

        compareAutomataOnLDL("[(false)*](tt)", declare, ps);

        compareAutomataOnLDL("[(false)*](ff)", declare, ps);

        compareAutomataOnLDL("[(a)*](tt)", declare, ps);

        compareAutomataOnLDL("[(a)*](ff)", declare, ps);
    }

    @Test
    public void compLTLToAutomataTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        compareAutomataOnLTL("true", declare, ps); //<true>tt

        compareAutomataOnLTL("false", declare, ps); //<false>tt

        compareAutomataOnLTL("a", declare, ps); //<a>tt

        compareAutomataOnLTL("!true", declare, ps); //<false>tt

        compareAutomataOnLTL("!false", declare, ps); //<true>tt

        compareAutomataOnLTL("!a", declare, ps); //<!a>tt

        compareAutomataOnLTL("F(a)", declare, ps);

        compareAutomataOnLTL("G(a)", declare, ps);

//        compareAutomataOnLTL("a U b", declare, ps); // RE_TEST

//        compareAutomataOnLTL("a W b", declare, ps); // RE_TEST

//        compareAutomataOnLTL("a R b", declare, ps); // RE_TEST

        compareAutomataOnLTL("a <-> b", declare, ps);

        compareAutomataOnLTL("last", declare, ps);
    }

    private void compareAutomataOnLTL(String input, boolean declare, PropositionalSignature ps) {
        LTLfFormula ltlfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = ltlfFormula.toLDLf();
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        if (!(new ModelCheck<>().test(ldlf2dfa, comp))) {
            printComparison(ldlf2dfa, comp, ldlfFormula);
        } else {
            System.out.println("Formula: " + ldlfFormula + " was OK");
        }
    }

    private void compareAutomataOnLDL(String input, boolean declare, PropositionalSignature ps) {
        LDLfFormula ldlfFormula = ParserUtils.parseLDLfFormula(input);
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        if (!(new ModelCheck<>().test(ldlf2dfa, comp))) {
            printComparison(ldlf2dfa, comp, ldlfFormula);
        } else {
            System.out.println("Formula: " + ldlfFormula + " was OK");
        }

    }

    private PropositionalSignature generateSignature() {
        PropositionalSignature ps = new PropositionalSignature();

        Proposition a = new Proposition("a");
        Proposition b = new Proposition("b");

        ps.add(a);
        ps.add(b);

        return ps;
    }

    private void printComparison(Automaton ldlf2dfa, Automaton comp, LDLfFormula formula) {
        System.out.println("Formula: " + formula + "\n");

        System.out.println("LDLf2DFA:");
        System.out.println(ldlf2dfa.toString());
        System.out.println("------------------------\n");

        System.out.println("Compositional:");
        System.out.println(comp.toString());
        System.out.println("------------------------\n");
    }
}
