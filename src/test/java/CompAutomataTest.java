import formula.FormulaType;
import formula.ldlf.*;
import formula.ltlf.LTLfFormula;
import formula.regExp.RegExp;
import formula.regExp.RegExpLocalVar;
import formula.regExp.RegExpTest;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import org.junit.Test;
import rationals.Automaton;
import rationals.properties.ModelCheck;
import rationals.transformations.Reducer;
import rationals.transformations.SinkComplete;
import rationals.transformations.Union;
import utils.AutomatonUtils;
import utils.CompAutomatonUtils;
import utils.FormulaUtils;
import utils.ParserUtils;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

public class CompAutomataTest {

    @Test
    public void convertAutomataTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        LDLfFormula formula = ParserUtils.parseLDLfFormula("<a>(tt)");
        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, formula, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);
        Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, formula, ps);
        Automaton comp2 = CompAutomatonUtils.convertLDLf2DFAtoCompositional(ldlf2dfa);

        Automaton orAutomaton = new Union<>().transform(ldlf2dfa, comp);
        orAutomaton = new Reducer<>().transform(orAutomaton);
        Automaton orAutomaton2 = new Union<>().transform(comp2, comp);
        orAutomaton2 = new Reducer<>().transform(orAutomaton2);

        printComparison(orAutomaton, orAutomaton2, formula);
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
        return CompAutomatonUtils.regexpHasTest(regExp);
    }

    @Test
    public void compLDLToAutomataTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

//        compareAutomataOnLDL("tt", declare, ps);
//
//        compareAutomataOnLDL("ff", declare, ps);
//
//        compareAutomataOnLDL("!(tt)", declare, ps);
//
//        compareAutomataOnLDL("!(ff)", declare, ps);
//
//        //diamond formulae
//        compareAutomataOnLDL("<true>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<true>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<false>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<false>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<a>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<a>(ff)", declare, ps);
//
//        //box formulae
//        compareAutomataOnLDL("[true](tt)", declare, ps);
//
//        compareAutomataOnLDL("[true](ff)", declare, ps); // end
//
//        compareAutomataOnLDL("[false](tt)", declare, ps);
//
//        compareAutomataOnLDL("[false](ff)", declare, ps);
//
//        compareAutomataOnLDL("[a](tt)", declare, ps);
//
//        compareAutomataOnLDL("[a](ff)", declare, ps);
//
//        compareAutomataOnLDL("[!(a)](tt)", declare, ps);
//
//        compareAutomataOnLDL("[!(a)](ff)", declare, ps);
//
//        //star diamond formulae
//        compareAutomataOnLDL("<(true)*>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<(true)*>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<(false)*>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<(false)*>(ff)", declare, ps);
//
//        compareAutomataOnLDL("<(a)*>(tt)", declare, ps);
//
//        compareAutomataOnLDL("<(a)*>(ff)", declare, ps);
//
//        //star box formulae
//        compareAutomataOnLDL("[(true)*](tt)", declare, ps);
//
//        compareAutomataOnLDL("[(true)*](ff)", declare, ps);
//
//        compareAutomataOnLDL("[(false)*](tt)", declare, ps);
//
//        compareAutomataOnLDL("[(false)*](ff)", declare, ps);
//
//        compareAutomataOnLDL("[(a)*](tt)", declare, ps);
//
//        compareAutomataOnLDL("[(a)*](ff)", declare, ps);

        //(<a>(tt)?)
        LDLfFormula att = ParserUtils.parseLDLfFormula("<a>(tt)");
        LDLfFormula end = ParserUtils.parseLDLfFormula("(end)");
        LDLfFormula notEnd = ParserUtils.parseLDLfFormula("<true>(tt)");
        LDLfFormula aEnd = ParserUtils.parseLDLfFormula("<a>(end)");
        LDLfFormula aTest = ParserUtils.parseLDLfFormula("<(<a>(tt))?>(end)");
        LDLfFormula bAndNotEnd = ParserUtils.parseLDLfFormula("(<b>(tt)) && (<true>(tt))");
        LDLfFormula aUb = ParserUtils.parseLDLfFormula("<(<a>(tt))? ; (true)>(<b>(tt) && <true>(tt))");
        LDLfFormula a = ParserUtils.parseLDLfFormula("a");
        Automaton compA = CompAutomatonUtils.getElementaryAutomaton(new RegExpLocalVar(new Proposition("a")), ps);
        Automaton compBandNotEnd = CompAutomatonUtils.LDLfToAutomaton(declare, bAndNotEnd, ps);
        compA = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.LDLf_DIAMOND, null, compA, compBandNotEnd);
        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, aEnd, ps);
        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);
        Automaton compAtt = CompAutomatonUtils.LDLfToAutomaton(declare, aEnd, ps);
        printComparison(ldlf2dfa, compAtt, aEnd);
//        System.out.println(ldlf2dfa);
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

//        compareAutomataOnLTL("true", declare, ps); //<true>tt
//
//        compareAutomataOnLTL("false", declare, ps); //<false>tt
//
//        compareAutomataOnLTL("a", declare, ps); //<a>tt
//
//        compareAutomataOnLTL("!true", declare, ps); //<false>tt
//
//        compareAutomataOnLTL("!false", declare, ps); //<true>tt
//
//        compareAutomataOnLTL("!a", declare, ps); //<!a>tt
//
//        compareAutomataOnLTL("F(a)", declare, ps);
//
//        compareAutomataOnLTL("G(a)", declare, ps);

        compareAutomataOnLTL("a U b", declare, ps); // RE_TEST
//
//        compareAutomataOnLTL("a W b", declare, ps); // RE_TEST
//
//        compareAutomataOnLTL("a R b", declare, ps); // RE_TEST

//        compareAutomataOnLTL("a <-> b", declare, ps);
//
//        compareAutomataOnLTL("last", declare, ps);
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



//        //a U b, <*((?(<a>(tt))) ; (true))>((<b>(tt)) TeAND (<true>(tt)))
//        Automaton r1 = compAutomataFromString("<b>(tt)", declare, ps);
//        Automaton r2 = compAutomataFromString("<true>(tt)", declare, ps);
//        Automaton phi = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.LDLf_TEMP_AND, null, r1, r2);
//
//        Automaton psi = compAutomataFromString("<a>(tt)", declare, ps);
//        Automaton l2 = compAutomataFromString("true", declare, ps);
//        Automaton psiAndPhi = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.LDLf_TEMP_AND, null, psi, phi);
//        Automaton l3 = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.RE_CONCAT, null, psi, l2);
//        Automaton end = compAutomataFromString("[true]ff", declare, ps); //end
//        Automaton l5 = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.RE_STAR, null, l3, end);
////        System.out.println(psiAndPhi);
//
////        Automaton a = compAutomataFromString("<((<a>(tt))?) ; (true)>((<b>(tt)) && (<true>(tt)))", declare, ps);
////        System.out.println(a);
//
////        compareAutomataOnLDL("<((<a>(tt))?) ; (true)>((<b>(tt)) && (<true>(tt)))", declare, ps);
//        LDLfFormula test = ParserUtils.parseLDLfFormula("<((<a>(tt))?)*>(<b>(tt))");
//        LDLfFormula att = ParserUtils.parseLDLfFormula("<a>(tt)");
//        LDLfFormula btt = ParserUtils.parseLDLfFormula("<b>(tt)");
//        Automaton ldlf2dfa = AutomatonUtils.ldlf2Automaton(declare, test, ps);
//        ldlf2dfa = new Reducer<>().transform(ldlf2dfa);
////        Automaton compComp = CompAutomatonUtils.LDLfToAutomaton(declare, test, ps);
//        Automaton compAtt = CompAutomatonUtils.LDLfToAutomaton(declare, att, ps);
//        Automaton compBtt = CompAutomatonUtils.LDLfToAutomaton(declare, btt, ps);
////        Automaton tt = CompAutomatonUtils.LDLfToAutomaton(declare, new LDLfttFormula(), ps);
////        compAtt = new SinkComplete().transform(compAtt);
////        compBtt = new SinkComplete().transform(compBtt);
//        Automaton compTest = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.RE_TEST, null, compAtt, null);
//        Automaton compStar = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.RE_STAR, null, compTest, end);
////        compStar = new SinkComplete().transform(compStar);
//        Automaton comp = CompAutomatonUtils.compositionAutomatonFactory(FormulaType.LDLf_DIAMOND, null, compStar, compBtt);
////        System.out.println(compAtt);
//        printComparison(ldlf2dfa, comp, test);
////        compareAutomataOnLDL("<(<a>(tt))?>(tt)", declare, ps);


//            case RE_TEST:
////                compAutomaton = left.clone();
//                compAutomaton = new Automaton();
//                HashMap<State, State> map = new HashMap<>();
//                Iterator<State> i1 = left.states().iterator();
//                while (i1.hasNext()) {
//                    State e = i1.next();
//                    State n = compAutomaton.addState(e.isInitial(), e.isTerminal());
//                    map.put(e, n);
//                }
//
//                Iterator<Transition<PossibleWorld>> i2 = left.delta().iterator();
//                while (i2.hasNext()) {
//                    Transition<PossibleWorld> t = i2.next();
//                    try {
//                        if (t.end().isTerminal() && t.start().equals(t.end())) { //Only alter looping transitions
//                            Set<State> initials = left.initials();
//                            for (State s : initials) {
//                                compAutomaton.addTransition(new Transition<>(map.get(t.start()), null, map.get(s)));
//                            }
//                            compAutomaton.addTransition(new Transition<>(map.get(t.start()), t.label(), map.get(t.end())));
//                        } else {
//                            compAutomaton.addTransition(new Transition<>(map.get(t.start()), t.label(), map.get(t.end())));
//                        }
//                    } catch (NoSuchStateException e) {
//                        e.printStackTrace();
//                    }
//                }
////                compAutomaton = left.clone();
//                break;

