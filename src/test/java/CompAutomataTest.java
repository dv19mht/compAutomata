import formula.ldlf.*;
import formula.ltlf.LTLfFormula;
import formula.regExp.RegExp;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import org.junit.Test;
import rationals.Automaton;
import rationals.properties.ModelCheck;
import rationals.properties.isEmpty;
import rationals.transformations.*;
import utils.AutomatonUtils;
import utils.CompAutomatonUtils;
import utils.ParserUtils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CompAutomataTest {


    @Test
    public void ldlf2nfaCompTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();
        LTLfFormula ltLfFormula;

//        compareLdlf2nfaWithLdlf2nfaComp("true", declare, ps); //<true>tt

//        compareLdlf2nfaWithLdlf2nfaComp("false", declare, ps); //<false>tt
//
//        compareLdlf2nfaWithLdlf2nfaComp("a", declare, ps); //<a>tt
//
//        compareLdlf2nfaWithLdlf2nfaComp("!true", declare, ps); //<false>tt
//
//        compareLdlf2nfaWithLdlf2nfaComp("!false", declare, ps); //<true>tt
//
//        compareLdlf2nfaWithLdlf2nfaComp("!a", declare, ps); //<!a>tt
//
//        compareLdlf2nfaWithLdlf2nfaComp("F(a)", declare, ps);
//
//        compareLdlf2nfaWithLdlf2nfaComp("G(a)", declare, ps);

//        compareLdlf2nfaWithLdlf2nfaComp("a U b", declare, ps); // RE_TEST

//        compareLdlf2nfaWithLdlf2nfaComp("a W b", declare, ps); // RE_TEST
//
//        compareLdlf2nfaWithLdlf2nfaComp("a R b", declare, ps); // RE_TEST
//
//        compareLdlf2nfaWithLdlf2nfaComp("a <-> b", declare, ps);
//
//        compareLdlf2nfaWithLdlf2nfaComp("last", declare, ps);

//        compareAutomataOnLTL("a U b", declare, ps);

//        compareAutomataOnLTL("((!((a) U ((a) && (b)))) R (!(c))) && ((!(b)) U (X(b)))", declare, ps);

//        compareAutomataOnLTL("((!(b)) U (X(b)))", declare, ps);

        //[*((?(<*((?(<a>(tt))) ; (true))>((<(a) AND (b)>(tt)) TeAND (<true>(tt))))) ; (true))](([c](ff)) TeOR ([true](ff)))
//        compareAutomataOnLDL("[(((<(((<a>(tt))?) ; (true))*>((<(a) && (b)>(tt)) && (<true>(tt))))?) ; (true))*](([c](ff)) || ([true](ff)))", declare, ps);

        //<*((?(<NOT(b)>(tt))) ; (true))>((<true>((<b>(tt)) TeAND (<true>(tt)))) TeAND (<true>(tt)))
//        compareAutomataOnLDL("<(((<!(b)>(tt))?) ; (true))*>((<true>((<b>(tt)) && (<true>(tt)))) && (<true>(tt)))", declare, ps);

//        ltLfFormula = ParserUtils.parseLTLfFormula("((!((a) U ((a) && (b)))) R (!(c))) && ((!(b)) U (X(b)))");
//        ps = ltLfFormula.getSignature();
//        compareAutomataOnLDL("[(((<(((<a>(tt))?) ; (true))*>((<(a) && (b)>(tt)) && (<true>(tt))))?) ; (true))*](([c](ff)) || ([true](ff))) && <(((<!(b)>(tt))?) ; (true))*>((<true>((<b>(tt)) && (<true>(tt)))) && (<true>(tt)))", declare, ps);

        ltLfFormula = ParserUtils.parseLTLfFormula("((!(!(!(b)))) U (X(((a) R (!(a))) R (X(c))))) && (((!(b)) R (!(((b) || (b)) && (c)))) R (b))");
        ps = ltLfFormula.getSignature();
        compareAutomataOnLTL("((!(!(!(b)))) U (X(((a) R (!(a))) R (X(c))))) && (((!(b)) R (!(((b) || (b)) && (c)))) R (b))", declare, ps);
    }

    @Test
    public void findTestFormula() {
        boolean hasTest;
        hasTest = checkRegExp("a U b");
        assertTrue(hasTest);

//        hasTest = checkRegExp("a W b");
//        assertTrue(hasTest);

        hasTest = checkRegExp("a R b");
        assertTrue(hasTest);

        hasTest = checkRegExp("F(a)");
        assertFalse(hasTest);

        hasTest = checkRegExp("G(a)");
        assertFalse(hasTest);
    }

    private boolean checkRegExp(String input) {
        LTLfFormula ltl = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        RegExp regExp = ((LDLfTempOpTempFormula) ldl).getRegExp();
        return CompAutomatonUtils.checkRegExpHasTest(regExp);
    }

    @Test
    public void compLDLToAutomataTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        compareAutomataOnLDL("tt", declare, ps);

        compareAutomataOnLDL("ff", declare, ps);

        compareAutomataOnLDL("!(tt)", declare, ps);

        compareAutomataOnLDL("!(ff)", declare, ps);

        // diamond formulae
        compareAutomataOnLDL("<true>(tt)", declare, ps);

        compareAutomataOnLDL("<true>(ff)", declare, ps);

        compareAutomataOnLDL("<false>(tt)", declare, ps);

        compareAutomataOnLDL("<false>(ff)", declare, ps);

        compareAutomataOnLDL("<a>(tt)", declare, ps);

        compareAutomataOnLDL("<a>(ff)", declare, ps);

        // box formulae
        compareAutomataOnLDL("[true](tt)", declare, ps);

        compareAutomataOnLDL("[true](ff)", declare, ps); // end

        compareAutomataOnLDL("[false](tt)", declare, ps);

        compareAutomataOnLDL("[false](ff)", declare, ps);

        compareAutomataOnLDL("[a](tt)", declare, ps);

        compareAutomataOnLDL("[a](ff)", declare, ps);

        compareAutomataOnLDL("[!(a)](tt)", declare, ps);

        compareAutomataOnLDL("[!(a)](ff)", declare, ps);

        // star diamond formulae
        compareAutomataOnLDL("<(true)*>(tt)", declare, ps);

        compareAutomataOnLDL("<(true)*>(ff)", declare, ps);

        compareAutomataOnLDL("<(false)*>(tt)", declare, ps);

        compareAutomataOnLDL("<(false)*>(ff)", declare, ps);

        compareAutomataOnLDL("<(a)*>(tt)", declare, ps);

        compareAutomataOnLDL("<(a)*>(ff)", declare, ps);
//
//        // star box formulae
        compareAutomataOnLDL("[(true)*](tt)", declare, ps);

        compareAutomataOnLDL("[(true)*](ff)", declare, ps);

        compareAutomataOnLDL("[(false)*](tt)", declare, ps);

        compareAutomataOnLDL("[(false)*](ff)", declare, ps);

        compareAutomataOnLDL("[(a)*](tt)", declare, ps);

        compareAutomataOnLDL("[(a)*](ff)", declare, ps);

        // test formulae
        compareAutomataOnLDL("<(<true>tt)?>(tt)", declare, ps);

        compareAutomataOnLDL("<(<true>tt)?>(ff)", declare, ps);

        compareAutomataOnLDL("<(<false>tt)?>(tt)", declare, ps);

        compareAutomataOnLDL("<(<false>tt)?>(ff)", declare, ps);

        compareAutomataOnLDL("<(<a>tt)?>(tt)", declare, ps);

        compareAutomataOnLDL("<(<a>tt)?>(ff)", declare, ps);

        // concat formulae
        compareAutomataOnLDL("<(<true>tt)? ; true>(tt)", declare, ps);

        compareAutomataOnLDL("<(<true>tt)? ; true>(ff)", declare, ps);

        compareAutomataOnLDL("<(<false>tt)? ; true>(tt)", declare, ps);

        compareAutomataOnLDL("<(<false>tt)? ; true>(ff)", declare, ps);

        compareAutomataOnLDL("<(<a>tt)? ; true>(tt)", declare, ps);

        compareAutomataOnLDL("<(<a>tt)? ; true>(ff)", declare, ps);
    }

    private Automaton compAutomataFromString(String input, boolean declare, PropositionalSignature ps) {
        LDLfFormula ldlfFormula = ParserUtils.parseLDLfFormula(input);
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        return comp;
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

        compareAutomataOnLTL("a U b", declare, ps); // RE_TEST

        compareAutomataOnLTL("a W b", declare, ps); // RE_TEST

        compareAutomataOnLTL("a R b", declare, ps); // RE_TEST

        compareAutomataOnLTL("a <-> b", declare, ps);

        compareAutomataOnLTL("last", declare, ps);
    }

    private void compareLdlf2nfaWithLdlf2nfaComp(String input, boolean declare, PropositionalSignature ps) {
        LTLfFormula ltlfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = ltlfFormula.toLDLf();
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.ldlf2nfaComp(declare, ldlfFormula, ps, Long.MAX_VALUE);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

//        if (!(new ModelCheck<>().test(ldlf2dfa, comp))) {
            printComparison(ldlf2dfa, comp, ldlfFormula);
//        } else {
//            System.out.println("Formula: " + ldlfFormula + " was OK");
//        }
    }

    private void compareAutomataOnLTL(String input, boolean declare, PropositionalSignature ps) {
        LTLfFormula ltlfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = ltlfFormula.toLDLf();
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        if (new ModelCheck<>().test(ldlf2dfa, comp) && (bothEmpty(comp, ldlf2dfa) || bothNotEmpty(comp, ldlf2dfa))) {
            System.out.println("Formula: " + ldlfFormula + " was OK");
        } else {
            System.out.println("Formula NOT OK");
            printComparison(ldlf2dfa, comp, ldlfFormula);
        }
    }

    private void compareAutomataOnLDL(String input, boolean declare, PropositionalSignature ps) {
        LDLfFormula ldlfFormula = ParserUtils.parseLDLfFormula(input);
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        if (new ModelCheck<>().test(ldlf2dfa, comp) && (bothEmpty(comp, ldlf2dfa) || bothNotEmpty(comp, ldlf2dfa))) {
            System.out.println("Formula: " + ldlfFormula + " was OK");
        } else {
            printComparison(ldlf2dfa, comp, ldlfFormula);
        }

    }

    private boolean bothNotEmpty(Automaton comp, Automaton ldlf2dfa) {
        return !(new isEmpty<>().test(ldlf2dfa)) && !(new isEmpty<>().test(comp));
    }

    private boolean bothEmpty(Automaton comp, Automaton ldlf2dfa) {
        return new isEmpty<>().test(ldlf2dfa) && new isEmpty<>().test(comp);
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
