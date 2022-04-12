import antlr4_generated.LTLfFormulaParserLexer;
import antlr4_generated.LTLfFormulaParserParser;
import formula.*;
import formula.ldlf.LDLfFormula;
import formula.ldlf.LDLfTempOpTempFormula;
import formula.ltlf.*;
import formula.regExp.RegExp;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.Test;
import rationals.Automaton;
import visitors.LTLfVisitors.LTLfVisitor;

import static org.junit.Assert.*;

public class ParseLTLfFormulaTest {
    LTLfFormula ltlA;
    LTLfFormula ltlB;
    LTLfFormula ltl;
    LDLfFormula ldl;

    @Test
    public void LDLfToAutomatonTest() {
        //input: atomic, atomic regexp, localVar regexp
        //which type to build?
        //Set<Q> states, Set<L> alphabet/labels, I initialState, Set<T> finalStates, Set<D> transitions

    }

    @Test
    public void stringParserTest() {
        Automaton automaton;

        stringToAutomaton("a");
        System.out.println("------------------------\n");

        stringToAutomaton("true");
        System.out.println("------------------------\n");

        stringToAutomaton("False");
        System.out.println("------------------------\n");

        stringToAutomaton("!a");
        System.out.println("------------------------\n");

        stringToAutomaton("a && b");
        System.out.println("------------------------\n");

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempAndFormula(ltlA, ltlB);
        System.out.println("ltl: " + ltl);
        ldl = ltl.toLDLf();
        System.out.println("ldl: " + ldl);
        ldl = (LDLfFormula) ldl.nnf();
        System.out.println("nnf: " + ldl);
        automaton = LDLfToAutomaton(ldl);
        assertNull(automaton);
        System.out.println("------------------------\n");

        stringToAutomaton("a || b");
        System.out.println("------------------------\n");

        stringToAutomaton("a -> b");
        System.out.println("------------------------\n");

        stringToAutomaton("X(a)");
        System.out.println("------------------------\n");

        stringToAutomaton("F(a)");
        System.out.println("------------------------\n");

        stringToAutomaton("G(a)");
        System.out.println("------------------------\n");

        stringToAutomaton("a U b");
        System.out.println("------------------------\n");

        stringToAutomaton("a W b");
        System.out.println("------------------------\n");

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfWeakUntilFormula(ltlA, ltlB);
        System.out.println("ltl: " + ltl);
        ldl = ltl.toLDLf();
        System.out.println("ldl: " + ldl);
        ldl = (LDLfFormula) ldl.nnf();
        System.out.println("nnf: " + ldl);
        automaton = LDLfToAutomaton(ldl);
        assertNull(automaton);
        System.out.println("------------------------\n");

        stringToAutomaton("a R b");
        System.out.println("------------------------\n");

        stringToAutomaton("a <-> b");
        System.out.println("------------------------\n");

        stringToAutomaton("last");
        System.out.println("------------------------\n");
    }

    private void stringToAutomaton(String input) {
        //1. parse input string to LTLfFormula
        ltl = parseLTLfFormula(input);
        System.out.println("ltl: " + ltl);

        //2. convert LTLfFormula to LDLfFormula
        ldl = ltl.toLDLf();
        System.out.println("ldl: " + ldl);

        //3. convert to normal negated form(?)
        ldl = (LDLfFormula) ldl.nnf();
        System.out.println("nnf: " + ldl);

        //4. parse LDLfFormula
        Automaton automaton = LDLfToAutomaton(ldl);
        assertNull(automaton);
    }

    private Automaton LDLfToAutomaton(LDLfFormula formula) {
        Automaton automaton = null;

        /*
        * Base case when the formula is an atomic proposition
        */
        if (formula instanceof AtomicFormula) {
            System.out.println("atomic: " + formula);
            return automaton;
        }

        /* Else parse subformula */
        if (formula instanceof UnaryFormula) {
            UnaryFormula uFormula = (UnaryFormula) formula;
            LDLfFormula nested = (LDLfFormula) uFormula.getNestedFormula();
            automaton = LDLfToAutomaton(nested);
        } else if (formula instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) formula;
            LDLfFormula left = (LDLfFormula) bFormula.getLeftFormula();
            LDLfFormula right = (LDLfFormula) bFormula.getRightFormula();
            Automaton leftAutomaton = LDLfToAutomaton(left);
            Automaton rightAutomaton = LDLfToAutomaton(right);
        } else if (formula instanceof TemporalFormula) {
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) formula;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();
            Automaton regAutomaton = regexpToAutomaton(reg);
            Automaton goalAutomaton = LDLfToAutomaton(goal);
        } else {
            throw new IllegalArgumentException("Illegal formula " + formula);
        }

        //perform automata operations on DFA returned from subformula

        return automaton;
    }

    private Automaton regexpToAutomaton(RegExp regExp) {
        Automaton automaton = null;

        /* Base case when expression is atomic proposition */
        if (regExp instanceof AtomicFormula) {
            System.out.println("atomic regexp: " + regExp);
            return automaton;
        } else if (regExp instanceof LocalFormula) {
            System.out.println("localVar regexp: " + regExp);
            return automaton;
        }

        /* Else parse subformula */
        if (regExp instanceof UnaryFormula) {
            UnaryFormula uFormula = (UnaryFormula) regExp;
            Formula nested = uFormula.getNestedFormula();
            if (nested instanceof RegExp) {
                automaton = regexpToAutomaton((RegExp) nested);
            } else if (nested instanceof LDLfFormula) {
                automaton = LDLfToAutomaton((LDLfFormula) nested); //Special case (RegExpTest)
            } else {
                throw new IllegalArgumentException("Nested formula of illegal type " + nested.getClass());
            }
        } else if (regExp instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) regExp;
            RegExp left = (RegExp) bFormula.getLeftFormula(); //Can be LDLfFormula?
            RegExp right = (RegExp) bFormula.getRightFormula(); //Can be LDLfFormula?
            Automaton leftAutomaton = regexpToAutomaton(left);
            Automaton rightAutomaton = regexpToAutomaton(right);
        } else if (regExp instanceof TemporalFormula) {
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) regExp;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();
            Automaton regAutomaton = regexpToAutomaton(reg);
            Automaton goalAutomaton = LDLfToAutomaton(goal);
        } else {
            throw new IllegalArgumentException("Illegal regexp " + regExp);
        }

        return automaton;
    }

    @Test
    public void LDLfToNnf() {
        //3. convert to normal negated form(?)
        ltl = parseLTLfFormula("a");
        ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        assertEquals("<a>(tt)", ldl.toString());

        ltl = parseLTLfFormula("a");
        ltl = new LTLfTempNotFormula(ltl);
        ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        assertEquals("[a](ff)", ldl.toString());

        ltl = parseLTLfFormula("last");
        ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        assertEquals("[true](([true](ff)) TeOR ([true](ff)))", ldl.toString());
    }

    @Test
    public void LTLfToLDLf() {
        //2. convert LTLfFormula to LDLfFormula
        ltlA = parseLTLfFormula("a");
        ldl = ltlA.toLDLf();
        assertEquals("<a>(tt)", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfTempNotFormula(ltlA);
        ldl = ltlA.toLDLf();
        assertEquals("TeNOT(<a>(tt))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempAndFormula(ltlA, ltlB);
        ldl = ltl.toLDLf();
        assertEquals("(<a>(tt)) TeAND (<b>(tt))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempOrFormula(ltlA, ltlB);
        ldl = ltl.toLDLf();
        assertEquals("(<a>(tt)) TeOR (<b>(tt))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempImplFormula(ltlA, ltlB);
        ldl = ltl.toLDLf();
        assertEquals("(NOT(<a>(tt))) TeOR (<b>(tt))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfNextFormula(ltlA);
        ldl = ltlA.toLDLf();
        assertEquals("<true>((<a>(tt)) TeAND (TeNOT([true](ff))))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfEventuallyFormula(ltlA);
        ldl = ltlA.toLDLf();
        assertEquals("<*(true)>((<a>(tt)) TeAND (TeNOT([true](ff))))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfGloballyFormula(ltlA);
        ldl = ltlA.toLDLf();
        assertEquals("TeNOT(<*(true)>((<NOT(a)>(tt)) TeAND (TeNOT([true](ff)))))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfUntilFormula(ltlA, ltlB);
        ldl = ltl.toLDLf();
        assertEquals("<*((?(<a>(tt))) ; (true))>((<b>(tt)) TeAND (TeNOT([true](ff))))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfWeakUntilFormula(ltlA, ltlB);
        ldl = ltl.toLDLf();
        assertEquals("(<*((?(<a>(tt))) ; (true))>((<b>(tt)) TeAND (TeNOT([true](ff))))) TeOR (TeNOT(<*(true)>((<NOT(a)>(tt)) TeAND (TeNOT([true](ff))))))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfReleaseFormula(ltlA, ltlB);
        ldl = ltl.toLDLf();
        assertEquals("TeNOT(<*((?(<NOT(a)>(tt))) ; (true))>((<NOT(b)>(tt)) TeAND (TeNOT([true](ff)))))", ldl.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempDoubleImplFormula(ltlA, ltlB);
        ldl = ltl.toLDLf();
        assertEquals("((NOT(<a>(tt))) TeOR (<b>(tt))) TeAND ((NOT(<b>(tt))) TeOR (<a>(tt)))", ldl.toString());

        ltlA = parseLTLfFormula("last");
        ltl = ltlA;
        ldl = ltl.toLDLf();
        assertEquals("TeNOT(<true>((<true>(tt)) TeAND (TeNOT([true](ff)))))", ldl.toString());

        ltlA = parseLTLfFormula("true");
        ltl = ltlA;
        ldl = ltl.toLDLf();
        assertEquals("<true>(tt)", ldl.toString());

        ltlA = parseLTLfFormula("False");
        ltl = ltlA;
        ldl = ltl.toLDLf();
        assertEquals("<false>(tt)", ldl.toString());
    }

    @Test
    public void stringToLTLfTest() {
        //1. parse input string to LTLfFormula
        LTLfFormula formula = parseLTLfFormula("a");
        assertEquals("a", formula.toString());

        formula = parseLTLfFormula("!a");
        assertEquals("NOT(a)", formula.toString());

        formula = parseLTLfFormula("a && b");
        assertEquals("(a) AND (b)", formula.toString());

        formula = parseLTLfFormula("a || b");
        assertEquals("(a) OR (b)", formula.toString());

        formula = parseLTLfFormula("a -> b");
        assertEquals("(a) IMPL (b)", formula.toString());

        formula = parseLTLfFormula("X(a)");
        assertEquals("X(a)", formula.toString());

        formula = parseLTLfFormula("F(a)");
        assertEquals("F(a)", formula.toString());

        formula = parseLTLfFormula("G(a)");
        assertEquals("G(a)", formula.toString());

        formula = parseLTLfFormula("a U b");
        assertEquals("(a) U (b)", formula.toString());

        formula = parseLTLfFormula("a W b");
        assertEquals("(a) WU (b)", formula.toString());

        formula = parseLTLfFormula("a R b");
        assertEquals("(a) R (b)", formula.toString());

        formula = parseLTLfFormula("a <-> b");
        assertEquals("(a) DOUBLEIMPL (b)", formula.toString());

        formula = parseLTLfFormula("last");
        assertEquals("TeNOT(X(true))", formula.toString());

        formula = parseLTLfFormula("true");
        assertEquals("true", formula.toString());

        formula = parseLTLfFormula("False");
        assertEquals("false", formula.toString());
    }

    private LTLfFormula parseLTLfFormula(String input){
        LTLfFormulaParserLexer lexer = new LTLfFormulaParserLexer(new ANTLRInputStream(input));
        LTLfFormulaParserParser parser = new LTLfFormulaParserParser(new CommonTokenStream(lexer));

        ParseTree tree = parser.expression();
        LTLfVisitor visitor = new LTLfVisitor();

        return visitor.visit(tree);
    }
}
