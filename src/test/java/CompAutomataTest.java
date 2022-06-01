import formula.ldlf.*;
import formula.ltlf.LTLfFormula;
import formula.quotedFormula.QuotedVar;
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
import automaton.QuotedFormulaStateFactory.QuotedFormulaState;

import java.util.Set;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

/**
 * @author Mathias Hedqvist 2022-06-03
 */
public class CompAutomataTest {

    /*
     * various formulae where bugs where found
     */
    @Test
    public void weirdFormulaeTest() {
        boolean declare = true;
        PropositionalSignature ps;
        LTLfFormula ltLfFormula;
        LDLfFormula ldlfFormula;

//        //[*((?(<*((?(<a>(tt))) ; (true))>((<(a) AND (b)>(tt)) TeAND (<true>(tt))))) ; (true))](([c](ff)) TeOR ([true](ff)))
//        ldlfFormula = ParserUtils.parseLDLfFormula("[(((<(((<a>(tt))?) ; (true))*>((<(a) && (b)>(tt)) && (<true>(tt))))?) ; (true))*](([c](ff)) || ([true](ff)))");
//        ps = ldlfFormula.getSignature();
//        compareCldlfOnLDL("[(((<(((<a>(tt))?) ; (true))*>((<(a) && (b)>(tt)) && (<true>(tt))))?) ; (true))*](([c](ff)) || ([true](ff)))", declare, ps);
//
//        //<*((?(<NOT(b)>(tt))) ; (true))>((<true>((<b>(tt)) TeAND (<true>(tt)))) TeAND (<true>(tt)))
//        ldlfFormula = ParserUtils.parseLDLfFormula("<(((<!(b)>(tt))?) ; (true))*>((<true>((<b>(tt)) && (<true>(tt)))) && (<true>(tt)))");
//        ps = ldlfFormula.getSignature();
//        compareCldlfOnLDL("<(((<!(b)>(tt))?) ; (true))*>((<true>((<b>(tt)) && (<true>(tt)))) && (<true>(tt)))", declare, ps);
//
//        ltLfFormula = ParserUtils.parseLTLfFormula("((!((a) U ((a) && (b)))) R (!(c))) && ((!(b)) U (X(b)))");
//        ps = ltLfFormula.getSignature();
//        compareCldlfOnLDL("[(((<(((<a>(tt))?) ; (true))*>((<(a) && (b)>(tt)) && (<true>(tt))))?) ; (true))*](([c](ff)) || ([true](ff))) && <(((<!(b)>(tt))?) ; (true))*>((<true>((<b>(tt)) && (<true>(tt)))) && (<true>(tt)))", declare, ps);
//
//        ltLfFormula = ParserUtils.parseLTLfFormula("((!(!(!(b)))) U (X(((a) R (!(a))) R (X(c))))) && (((!(b)) R (!(((b) || (b)) && (c)))) R (b))");
//        ps = ltLfFormula.getSignature();
//        compareCldlfOnLTL("((!(!(!(b)))) U (X(((a) R (!(a))) R (X(c))))) && (((!(b)) R (!(((b) || (b)) && (c)))) R (b))", declare, ps);

        // formula below actually takes much longer for c-ldlf (due to stripping of the last TeAND (b) )
//        //((TeNOT(TeNOT(TeNOT(((((NOT(a)) U (c)) U (X((NOT(c)) R (a)))) TeAND (X(a))) TeOR (((X(b)) R (X(c))) TeOR (a)))))) U ((b) U (b))) TeAND (b)
//        ltLfFormula = ParserUtils.parseLTLfFormula("((!(!(!(((((!(a)) U (c)) U (X((!(c)) R (a)))) && (X(a))) || (((X(b)) R (X(c))) || (a)))))) U ((b) U (b))) && (b)");
//        ldlfFormula = ltLfFormula.toLDLf();
//        ps = ltLfFormula.getSignature();
//        long timeStarted = System.currentTimeMillis();
//        Automaton a1 = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
//        long timeElapsed = System.currentTimeMillis() - timeStarted;
//        System.out.println("formula with (&& b): " + timeElapsed);
//
//        ltLfFormula = ParserUtils.parseLTLfFormula("((!(!(!(((((!(a)) U (c)) U (X((!(c)) R (a)))) && (X(a))) || (((X(b)) R (X(c))) || (a)))))) U ((b) U (b)))"); // no && (b) at the end
//        ldlfFormula = ltLfFormula.toLDLf();
//        ps = ltLfFormula.getSignature();
//        timeStarted = System.currentTimeMillis();
//        Automaton a2 = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
//        timeElapsed = System.currentTimeMillis() - timeStarted;
//        System.out.println("formula wo (&& b): " + timeElapsed);

//        compareAutomataOnLTLTime("((!(!(!(((((!(a)) U (c)) U (X((!(c)) R (a)))) && (X(a))) || (((X(b)) R (X(c))) || (a)))))) U ((b) U (b))) && (b)", declare, ps);

//        //((a) U (X(i))) TeAND (X(X((X(((i) TeOR (h)) R (j))) TeAND (h))))
//        ltLfFormula = ParserUtils.parseLTLfFormula("((a) U (X(i))) && (X(X((X(((i) || (h)) R (j))) && (h))))");
//        ps = ltLfFormula.getSignature();
//        compareCldlfOnLTL("((a) U (X(i))) && (X(X((X(((i) || (h)) R (j))) && (h))))", declare, ps);
//
//        //((TeNOT(TeNOT(NOT(e)))) U (X(((e) R (NOT(a))) R (X(d))))) TeAND (((NOT(h)) R (TeNOT(((h) TeOR (j)) TeAND (j)))) R (h))
//        ltLfFormula = ParserUtils.parseLTLfFormula("((!(!(!(e)))) U (X(((e) R (!(a))) R (X(d))))) && (((!(h)) R (!(((h) || (j)) && (j)))) R (h))");
//        ps = ltLfFormula.getSignature();
//        compareCldlfOnLTL("((!(!(!(e)))) U (X(((e) R (!(a))) R (X(d))))) && (((!(h)) R (!(((h) || (j)) && (j)))) R (h))", declare, ps);
//
//        //((!(!(!(e)))) U (X(((e) R (!(a))) R (X(d)))))
//        //&& (((!(h)) R (!(((h) || (j)) && (j)))) R (h))
//        ltLfFormula = ParserUtils.parseLTLfFormula("((!(!(!(e)))) U (X(((e) R (!(a))) R (X(d)))))");
//        ps = ltLfFormula.getSignature();
//        compareCldlfOnLTL("((!(!(!(e)))) U (X(((e) R (!(a))) R (X(d)))))", declare, ps);
//
//        //(TeNOT((NOT(a)) U (g))) TeAND (TeNOT(TeNOT(X((TeNOT(X(((h) R (NOT(h))) R (X(j))))) TeOR (f)))))
//        ltLfFormula = ParserUtils.parseLTLfFormula("(!((!(a)) U (g))) && (!(!(X((!(X(((h) R (!(h))) R (X(j))))) || (f)))))");
//        ps = ltLfFormula.getSignature();
//        compareTopCldlfOnLTL("(!((!(a)) U (g))) && (!(!(X((!(X(((h) R (!(h))) R (X(j))))) || (f)))))", declare, ps);

        // TopCLDLf takes much longer than LDLf2NFA
        //(TeNOT(((X(X(d))) U (X(c))) R ((X(X(NOT(b)))) TeAND (NOT(b))))) TeAND ((X(h)) TeAND ((TeNOT(X(i))) R (TeNOT((TeNOT(TeNOT(X(a)))) TeOR (j)))))

        //(((((i) R (X(b))) TeAND (((TeNOT((X(NOT(c))) U ((e) TeAND ((NOT(c)) TeAND ((c) TeOR (g)))))) U ((e) TeAND (f))) TeAND (X((h) U (e))))) R (X(h))) U (e)) TeAND (X(a))

        //2580s c-ldlf, 12s ldlf2nfa, gives heap space error when used only with ldlf2nfaComp
        //((TeNOT(X(((X((c) R (c))) R (X(d))) R (f)))) U (X((NOT(h)) TeOR (X((f) TeOR (X(TeNOT(X(NOT(a)))))))))) TeAND ((X(e)) U (X(g)))

//        //7282 states c-ldlf, 78 states ldlf2nfa (only happens when time out set to 100s, no error when running full time)
//        //(((((a) U (j)) TeAND ((c) TeAND ((e) TeAND (X(c))))) R ((b) U (b))) TeOR (c)) TeAND ((TeNOT(((e) TeAND (X((((c) U (a)) R (X(f))) U (NOT(a))))) U (((X(NOT(j))) U (g)) R (f)))) U (d))
        ltLfFormula = ParserUtils.parseLTLfFormula("(((((a) U (j)) && ((c) && ((e) && (X(c))))) R ((b) U (b))) || (c)) && ((!(((e) && (X((((c) U (a)) R (X(f))) U (!(a))))) U (((X(!(j))) U (g)) R (f)))) U (d))");
        ps = ltLfFormula.getSignature();
        compareCldlfOnLTL("(((((a) U (j)) && ((c) && ((e) && (X(c))))) R ((b) U (b))) || (c)) && ((!(((e) && (X((((c) U (a)) R (X(f))) U (!(a))))) U (((X(!(j))) U (g)) R (f)))) U (d))", declare, ps);
    }

    private void compareTopWeirdFormula(String input) {
        boolean declare = true;
        LTLfFormula ltLfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = (LDLfFormula) ltLfFormula.toLDLf().nnf();
        PropositionalSignature ps = ldlfFormula.getSignature();
        System.out.println(ldlfFormula);

        Automaton a1 = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps, 100000);
        System.out.println("states " + a1.states().size() + " trans " + a1.delta().size());
//        printAutomatonStates(a1);
        a1 = new Reducer<>().transform(a1);
        System.out.println("reduced:");
        System.out.println("states " + a1.states().size() + " trans " + a1.delta().size());
        System.out.println();

        Automaton a2 = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps, System.currentTimeMillis(), 100000);
        System.out.println("states " + a2.states().size() + " trans " + a2.delta().size());
//        printAutomatonStates(a2);
        a2 = new Reducer<>().transform(a2);
        System.out.println("reduced:");
        System.out.println("states " + a2.states().size() + " trans " + a2.delta().size());
    }

    private void printAutomatonStates(Automaton automaton) {
        for (QuotedFormulaState s : (Set<QuotedFormulaState>) automaton.states()) {
            Set<QuotedVar> formulaSet = s.getFormulaSet();
            if (formulaSet != null && !formulaSet.isEmpty()) {
                System.out.println(s + " " + s.getQuotedConjunction());
            } else {
                System.out.println(s);
            }
        }
    }

    @Test
    public void compareTopCldlfOnLTLTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        compareTopCldlfOnLTL("true", declare, ps); //<true>tt

        compareTopCldlfOnLTL("false", declare, ps); //<false>tt

        compareTopCldlfOnLTL("a", declare, ps); //<a>tt

        compareTopCldlfOnLTL("!true", declare, ps); //<false>tt

        compareTopCldlfOnLTL("!false", declare, ps); //<true>tt

        compareTopCldlfOnLTL("!a", declare, ps); //<!a>tt

        compareTopCldlfOnLTL("F(a)", declare, ps);

        compareTopCldlfOnLTL("G(a)", declare, ps);

        compareTopCldlfOnLTL("a U b", declare, ps); // RE_TEST

        compareTopCldlfOnLTL("a W b", declare, ps); // RE_TEST

        compareTopCldlfOnLTL("a R b", declare, ps); // RE_TEST

        compareTopCldlfOnLTL("a <-> b", declare, ps);

        compareTopCldlfOnLTL("last", declare, ps);
    }

    @Test
    public void compareCldlfOnLDLTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        compareCldlfOnLDL("tt", declare, ps);

        compareCldlfOnLDL("ff", declare, ps);

        compareCldlfOnLDL("!(tt)", declare, ps);

        compareCldlfOnLDL("!(ff)", declare, ps);

        // diamond formulae
        compareCldlfOnLDL("<true>(tt)", declare, ps);

        compareCldlfOnLDL("<true>(ff)", declare, ps);

        compareCldlfOnLDL("<false>(tt)", declare, ps);

        compareCldlfOnLDL("<false>(ff)", declare, ps);

        compareCldlfOnLDL("<a>(tt)", declare, ps);

        compareCldlfOnLDL("<a>(ff)", declare, ps);

        // box formulae
        compareCldlfOnLDL("[true](tt)", declare, ps);

        compareCldlfOnLDL("[true](ff)", declare, ps); // end

        compareCldlfOnLDL("[false](tt)", declare, ps);

        compareCldlfOnLDL("[false](ff)", declare, ps);

        compareCldlfOnLDL("[a](tt)", declare, ps);

        compareCldlfOnLDL("[a](ff)", declare, ps);

        compareCldlfOnLDL("[!(a)](tt)", declare, ps);

        compareCldlfOnLDL("[!(a)](ff)", declare, ps);

        // star diamond formulae
        compareCldlfOnLDL("<(true)*>(tt)", declare, ps);

        compareCldlfOnLDL("<(true)*>(ff)", declare, ps);

        compareCldlfOnLDL("<(false)*>(tt)", declare, ps);

        compareCldlfOnLDL("<(false)*>(ff)", declare, ps);

        compareCldlfOnLDL("<(a)*>(tt)", declare, ps);

        compareCldlfOnLDL("<(a)*>(ff)", declare, ps);
//
//        // star box formulae
        compareCldlfOnLDL("[(true)*](tt)", declare, ps);

        compareCldlfOnLDL("[(true)*](ff)", declare, ps);

        compareCldlfOnLDL("[(false)*](tt)", declare, ps);

        compareCldlfOnLDL("[(false)*](ff)", declare, ps);

        compareCldlfOnLDL("[(a)*](tt)", declare, ps);

        compareCldlfOnLDL("[(a)*](ff)", declare, ps);

        // test formulae
        compareCldlfOnLDL("<(<true>tt)?>(tt)", declare, ps);

        compareCldlfOnLDL("<(<true>tt)?>(ff)", declare, ps);

        compareCldlfOnLDL("<(<false>tt)?>(tt)", declare, ps);

        compareCldlfOnLDL("<(<false>tt)?>(ff)", declare, ps);

        compareCldlfOnLDL("<(<a>tt)?>(tt)", declare, ps);

        compareCldlfOnLDL("<(<a>tt)?>(ff)", declare, ps);

        // concat formulae
        compareCldlfOnLDL("<(<true>tt)? ; true>(tt)", declare, ps);

        compareCldlfOnLDL("<(<true>tt)? ; true>(ff)", declare, ps);

        compareCldlfOnLDL("<(<false>tt)? ; true>(tt)", declare, ps);

        compareCldlfOnLDL("<(<false>tt)? ; true>(ff)", declare, ps);

        compareCldlfOnLDL("<(<a>tt)? ; true>(tt)", declare, ps);

        compareCldlfOnLDL("<(<a>tt)? ; true>(ff)", declare, ps);
    }

    @Test
    public void compareCldlfOnLTLTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        compareCldlfOnLTL("true", declare, ps); //<true>tt

        compareCldlfOnLTL("false", declare, ps); //<false>tt

        compareCldlfOnLTL("a", declare, ps); //<a>tt

        compareCldlfOnLTL("!true", declare, ps); //<false>tt

        compareCldlfOnLTL("!false", declare, ps); //<true>tt

        compareCldlfOnLTL("!a", declare, ps); //<!a>tt

        compareCldlfOnLTL("F(a)", declare, ps);

        compareCldlfOnLTL("G(a)", declare, ps);

        compareCldlfOnLTL("a U b", declare, ps); // RE_TEST

        compareCldlfOnLTL("a W b", declare, ps); // RE_TEST

        compareCldlfOnLTL("a R b", declare, ps); // RE_TEST

        compareCldlfOnLTL("a <-> b", declare, ps);

        compareCldlfOnLTL("last", declare, ps);
    }

    @Test
    public void findTestFormula() {
        boolean hasTest;

        hasTest = checkForTestsTest("true");
        assertFalse(hasTest);

        hasTest = checkForTestsTest("false");
        assertFalse(hasTest);

        hasTest = checkForTestsTest("a");
        assertFalse(hasTest);

        hasTest = checkForTestsTest("F(a)");
        assertFalse(hasTest);

        hasTest = checkForTestsTest("G(a)");
        assertFalse(hasTest);

        hasTest = checkForTestsTest("a U b");
        assertTrue(hasTest);

        hasTest = checkForTestsTest("a W b");
        assertTrue(hasTest);

        hasTest = checkForTestsTest("a R b");
        assertTrue(hasTest);

        hasTest = checkForTestsTest("a <-> b");
        assertFalse(hasTest);

        hasTest = checkForTestsTest("last");
        assertFalse(hasTest);
    }

    private void compareTopCldlfOnLTL(String input, boolean declare, PropositionalSignature ps) {
        LTLfFormula ltlfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = ltlfFormula.toLDLf();
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.ldlf2nfaComp(declare, ldlfFormula, ps, Long.MAX_VALUE);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2nfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2nfa = new Reducer<>().transform(ldlf2nfa);

        System.out.println("Formula: " + ldlfFormula);
        modelCheckAutomata(ldlf2nfa, comp);
    }

    private void compareTopCldlfOnLDL(String input, boolean declare, PropositionalSignature ps) {
        LDLfFormula ldlfFormula = ParserUtils.parseLDLfFormula(input);
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.ldlf2nfaComp(declare, ldlfFormula, ps, Long.MAX_VALUE);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        System.out.println("Formula: " + ldlfFormula);
        modelCheckAutomata(ldlf2dfa, comp);
    }

    private void compareCldlfOnLTL(String input, boolean declare, PropositionalSignature ps) {
        LTLfFormula ltlfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = ltlfFormula.toLDLf();
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        System.out.println("Formula: " + ldlfFormula);
        modelCheckAutomata(ldlf2dfa, comp);
    }

    private void compareCldlfOnLTLTime(String input, boolean declare, PropositionalSignature ps) {
        LTLfFormula ltlfFormula = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldlfFormula = ltlfFormula.toLDLf();
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        long compStart = System.currentTimeMillis();
        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);
        long compElapsed = System.currentTimeMillis() - compStart;

        long ldlf2nfaStart = System.currentTimeMillis();
        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        System.out.println("states: " + ldlf2dfa.states().size());
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);
        long ldlf2nfaElapsed = System.currentTimeMillis() - ldlf2nfaStart;

        System.out.println("Formula: " + ldlfFormula);
        modelCheckAutomata(ldlf2dfa, comp);

        System.out.println("Time comp: " + compElapsed);
        System.out.println("Time ldlf2nfa: " + ldlf2nfaElapsed);
    }

    private void compareCldlfOnLDL(String input, boolean declare, PropositionalSignature ps) {
        LDLfFormula ldlfFormula = ParserUtils.parseLDLfFormula(input);
        ldlfFormula = (LDLfFormula) ldlfFormula.nnf();

        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, ldlfFormula, ps);
        comp = new Reducer<>().transform(comp);

        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);

        System.out.println("Formula: " + ldlfFormula);
        modelCheckAutomata(ldlf2dfa, comp);
    }

    private void modelCheckAutomata(Automaton ldlf2dfa, Automaton comp) {
        ModelCheck modelCheck = new ModelCheck<>();

        if (modelCheck.test(ldlf2dfa, comp) && (bothEmpty(comp, ldlf2dfa) || bothNotEmpty(comp, ldlf2dfa))) {
            System.out.println("Formula OK");
        } else {
            System.out.println("Formula NOT OK");
            printComparison(ldlf2dfa, comp);
        }

        if (modelCheck.test(comp, ldlf2dfa) && (bothEmpty(comp, ldlf2dfa) || bothNotEmpty(comp, ldlf2dfa))) {
            System.out.println("Formula OK");
        } else {
            System.out.println("Formula NOT OK");
            printComparison(ldlf2dfa, comp);
        }
    }

    private boolean checkForTestsTest(String input) {
        LDLfFormula ldl = CompAutomatonUtils.stringToNnfLDLf(input);
        return CompAutomatonUtils.checkForTestWithinStar(ldl);
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

    private void printComparison(Automaton ldlf2dfa, Automaton comp) {
        System.out.println("LDLf2NFA:");
        System.out.println(ldlf2dfa.toString());
        System.out.println("------------------------\n");

        System.out.println("C-LDLf:");
        System.out.println(comp.toString());
        System.out.println("------------------------\n");
    }
}
