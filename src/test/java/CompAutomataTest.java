import formula.ldlf.LDLfFormula;
import formula.ltlf.LTLfFormula;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import org.junit.Test;
import rationals.Automaton;
import rationals.transformations.Reducer;
import utils.AutomatonUtils;
import utils.CompAutomatonUtils;
import utils.ParserUtils;

public class CompAutomataTest {

    @Test
    public void compLDLToAutomataTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

//        compareAutomataOnLDL("true", declare, ps);
//
//        compareAutomataOnLDL("false", declare, ps);
//
//        compareAutomataOnLDL("a", declare, ps);


//        compareAutomataOnLDL("!true", declare, ps);
//
//        compareAutomataOnLDL("!false", declare, ps);
//
//        compareAutomataOnLDL("!(a)", declare, ps);


//        compareAutomataOnLDL("a && b", declare, ps);
//
//        compareAutomataOnLDL("a || b", declare, ps);
//
//        compareAutomataOnLDL("tt", declare, ps);
//
//        compareAutomataOnLDL("ff", declare, ps);
//
//        compareAutomataOnLDL("!(tt)", declare, ps);
//
//        compareAutomataOnLDL("!(ff)", declare, ps);

        //diamond formulae
//        compareAutomataOnLDL("<true>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<true>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<true>(a)", declare, ps);
//
//        compareAutomataOnLDL("<true>(!(a))", declare, ps);
//
//        compareAutomataOnLDL("<false>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<false>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<false>(a)", declare, ps);
//
//        compareAutomataOnLDL("<false>(!(a))", declare, ps);
//
//        compareAutomataOnLDL("<a>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<a>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<a>(a)", declare, ps);
//
//        compareAutomataOnLDL("<a>(!(a))", declare, ps);

        //box formulae
//        compareAutomataOnLDL("[true](tt)", declare, ps);
//
//        compareAutomataOnLDL("[true](ff)", declare, ps); // end
//
//        compareAutomataOnLDL("[true](a)", declare, ps);
//
//        compareAutomataOnLDL("[true](!(a))", declare, ps);
//
//        compareAutomataOnLDL("[false](tt)", declare, ps);
//
//        compareAutomataOnLDL("[false](ff)", declare, ps);
//
//        compareAutomataOnLDL("[false](a)", declare, ps);
//
//        compareAutomataOnLDL("[false](!(a))", declare, ps);
//
//        compareAutomataOnLDL("[a](tt)", declare, ps);
//
//        compareAutomataOnLDL("[a](ff)", declare, ps);
//
//        compareAutomataOnLDL("[a](a)", declare, ps);
//
//        compareAutomataOnLDL("[a](!(a))", declare, ps);
//
//        compareAutomataOnLDL("[!(a)](tt)", declare, ps);
//
//        compareAutomataOnLDL("[!(a)](ff)", declare, ps);
//
//        compareAutomataOnLDL("[!(a)](a)", declare, ps);
//
//        compareAutomataOnLDL("[!(a)](!(a))", declare, ps);

        //star diamond formulae
//        compareAutomataOnLDL("<(true)*>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<(true)*>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<(true)*>(a)", declare, ps); // Not correct(?) (MyConcatenation)
//
//        compareAutomataOnLDL("<(true)*>(!(a))", declare, ps);

//        compareAutomataOnLDL("<(false)*>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<(false)*>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<(false)*>(a)", declare, ps); // Reduces alphabet to 'a'
//
//        compareAutomataOnLDL("<(false)*>(!(a))", declare, ps); // Reduces alphabet to 'b'
//
//        compareAutomataOnLDL("<(a)*>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<(a)*>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<(a)*>(a)", declare, ps); // Reduces alphabet to 'a'
//
//        compareAutomataOnLDL("<(a)*>(!(a))", declare, ps);

        //star box formulae
//        compareAutomataOnLDL("[(true)*](tt)", declare, ps);
//
//        compareAutomataOnLDL("[(true)*](ff)", declare, ps);
//
//        compareAutomataOnLDL("[(true)*](a)", declare, ps);
//
//        compareAutomataOnLDL("[(true)*](!(a))", declare, ps);
//
//        compareAutomataOnLDL("[(false)*](tt)", declare, ps);

//        compareAutomataOnLDL("[(false)*](ff)", declare, ps);

//        compareAutomataOnLDL("[(false)*](a)", declare, ps);
//
//        compareAutomataOnLDL("[(false)*](!(a))", declare, ps);
//
        compareAutomataOnLDL("[(a)*](tt)", declare, ps);

        compareAutomataOnLDL("[(a)*](ff)", declare, ps);

        compareAutomataOnLDL("[(a)*](a)", declare, ps); // Reduces alphabet to 'a'

        compareAutomataOnLDL("[(a)*](!(a))", declare, ps);
    }

    @Test
    public void compLTLToAutomataTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

//        compareAutomataOnLTL("true", declare, ps); //<true>tt
//
//        compareAutomataOnLTL("false", declare, ps); //<false>tt
//
//        compareAutomataOnLTL("a", declare, ps); //<a>tt

//        compareAutomataOnLTL("!true", declare, ps); //<false>tt
//
//        compareAutomataOnLTL("!false", declare, ps); //<true>tt

//        compareAutomataOnLTL("!a", declare, ps); //<!a>tt

//        compareAutomataOnLTL("F(a)", declare, ps);

//        compareAutomataOnLTL("G(a)", declare, ps); // Not correct (MyConcatenation)
    }

    private void compareAutomataOnLTL(String input, boolean declare, PropositionalSignature ps) {
        LTLfFormula ltlfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = ltlfFormula.toLDLf();
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        printComparison(ldlf2dfa, comp, ldlfFormula);
    }

    private void compareAutomataOnLDL(String input, boolean declare, PropositionalSignature ps) {
        LDLfFormula ldlfFormula = ParserUtils.parseLDLfFormula(input);
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        printComparison(ldlf2dfa, comp, ldlfFormula);
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