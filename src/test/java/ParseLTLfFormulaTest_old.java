import antlr4_generated.LTLfFormulaParserLexer;
import antlr4_generated.LTLfFormulaParserParser;
import antlr4_generated.PropFormulaParserLexer;
import antlr4_generated.PropFormulaParserParser;
import compositionalUtils.MyConcatenation;
import formula.*;
import formula.ldlf.*;
import formula.ltlf.*;
import formula.regExp.RegExp;
import formula.regExp.RegExpLocal;
import formula.regExp.RegExpLocalTrue;
import formula.regExp.RegExpLocalVar;
import net.sf.tweety.logics.pl.semantics.PossibleWorld;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.Test;
import rationals.Automaton;
import rationals.NoSuchStateException;
import rationals.State;
import rationals.Transition;
import rationals.transformations.*;
import utils.AutomatonUtils;
import visitors.LTLfVisitors.LTLfVisitor;
import visitors.PropVisitor.LocalVisitor;

import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

public class ParseLTLfFormulaTest_old {
    LTLfFormula ltlA;
    LTLfFormula ltlB;
    LTLfFormula ltl;
    LDLfFormula ldlA;

    String strA = "a";
    String strNotA = "!a";
    String strAandB = "a && b";
    String strAorB = "a || b";
    String strAimplB = "a -> b";
    String strNextA = "X(a)";
    String strEventuallyA = "F(a)";
    String strGlobalA = "G(a)";
    String strAuntilB = "a U b";
    String strAweakUntilB = "a W b";
    String strAreleaseB = "a R B";
    String strAdoubleImpB = "a <-> b";
    String strLast = "last";
    String strTrue = "true";
    String strFalse = "False";

    @Test
    public void customElementaryAutomatonTest() {
        Proposition a = new Proposition("a");
        PropositionalSignature ps = generateSignature();
        Automaton comp;

        // a
        ldlA = new LDLfLocalVar(a);
        comp = getElementaryAutomaton(ldlA, ps);
        System.out.println("Formula: " + ldlA);
        System.out.println(comp.toString());

        // true
        ldlA = new LDLfLocalTrueFormula();
        comp = getElementaryAutomaton(ldlA, ps);
        System.out.println("Formula: " + ldlA);
        System.out.println(comp.toString());

        // false
        ldlA = new LDLfLocalFalseFormula();
        comp = getElementaryAutomaton(ldlA, ps);
        System.out.println("Formula: " + ldlA);
        System.out.println(comp.toString());

        // tt
        ldlA = new LDLfttFormula();
        comp = getElementaryAutomaton(ldlA, ps);
        System.out.println("Formula: " + ldlA);
        System.out.println(comp.toString());

        // ff
        ldlA = new LDLfffFormula();
        comp = getElementaryAutomaton(ldlA, ps);
        System.out.println("Formula: " + ldlA);
        System.out.println(comp.toString());
    }

    @Test
    public void compAutomatonTest() {
//        ldlA = stringToLDLf(strTrue);
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strFalse);
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strA);
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strNotA);
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strAandB); //Unsatisfiable regexp when declare is true (a && b can not be true at the same time).
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strAorB);
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strAimplB);
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strNextA);
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strEventuallyA); //RE_STAR not implemented yet
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strGlobalA); //RE_STAR not implemented yet
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strAuntilB); //RE_TEST not implemented yet
//        createAutomataPrintResults(ldlA);
//        Automaton automaton = AutomatonUtils.ldlf2Automaton(true, ldlA, generateSignature());
//        automaton = new Reducer<>().transform(automaton);
//        System.out.println("Formula: " + ldlA);
//        System.out.println(automaton);

//        ldlA = stringToLDLf(strAweakUntilB); //RE_TEST not implemented yet
//        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strAreleaseB); //RE_TEST not implemented yet
//        createAutomataPrintResults(ldlA);

        ldlA = stringToLDLf(strAdoubleImpB);
        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strLast);
//        createAutomataPrintResults(ldlA);
    }

    private void createAutomataPrintResults(LDLfFormula formula) {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();
        Automaton automaton;
        Automaton comp;

        automaton = AutomatonUtils.ldlf2Automaton(declare, formula, ps);
        automaton = new Reducer<>().transform(automaton);
        comp = LDLfToAutomaton(declare, formula, ps);
        comp = new Reducer<>().transform(comp);
        printComparison(automaton, comp, formula);
//        assertEquals(automaton.toString(), comp.toString());
    }


    @Test
    public void stringToPropFormula() {
        Proposition a = new Proposition("a");
        Proposition b = new Proposition("b");
        PropositionalFormula aANDb = new Conjunction(a, b);
        System.out.println(aANDb);
        ldlA = parseLocalFormula(aANDb.toString());
        System.out.println(ldlA);
    }

    @Test
    public void elementaryLdlf2DFACompTest() {
        boolean declare = true;
        Automaton automaton;
        Automaton comp;
        Automaton comp2;
        Automaton comp3;
        Automaton comp4;
        Automaton left;
        Automaton right;
        Automaton left2;
        Automaton right2;
        Automaton left3;
        Automaton right3;
        LDLfFormula ldlA;
        LDLfFormula ldlB;
        RegExp regExp;
        RegExp regExp2;
        LDLfFormula regExpLDLf;
        PropositionalSignature ps = generateSignature();
        Proposition a = new Proposition("a");
        Proposition b = new Proposition("b");

//        // true
//        ldlA = new LDLfLocalTrueFormula();
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), automaton, null);
//        automaton = new Reducer<>().transform(automaton);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // false
//        ldlA = new LDLfLocalFalseFormula();
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), automaton, null);
//        automaton = new Reducer<>().transform(automaton);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());

        // a
        ldlA = new LDLfLocalVar(a);
        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
        comp = compositionAutomatonFactory(ldlA.getFormulaType(), automaton, null);
        automaton = new Reducer<>().transform(automaton);
        comp = new Reducer<>().transform(comp);
        printComparison(automaton, comp, ldlA);
        assertEquals(automaton.toString(), comp.toString());
//
//        // !a
//        ldlA = new LDLfLocalVar(a);
//        left = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlA = new LDLfLocalNotFormula(ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, null);
//        automaton = new Reducer<>().transform(automaton);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString()); // Not the same, accepts epsilon
//
//        // a && b
//        ldlA = new LDLfLocalVar(a);
//        left = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlB = new LDLfLocalVar(b);
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
//        ldlA = new LDLfLocalAndFormula(ldlA, ldlB);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // a || b
//        ldlA = new LDLfLocalVar(a);
//        left = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlB = new LDLfLocalVar(b);
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
//        ldlA = new LDLfLocalOrFormula(ldlA, ldlB);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // <true>ff
//        regExp = new RegExpLocalTrue();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = AutomatonUtils.ldlf2Automaton(declare, regExpLDLf, ps);
//        ldlA = new LDLfffFormula();
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlA = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // <false>tt
//        regExp = new RegExpLocalFalse();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = AutomatonUtils.ldlf2Automaton(declare, regExpLDLf, ps);
//        ldlA = new LDLfLocalTrueFormula();
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlA = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // <a>tt
//        regExp = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = AutomatonUtils.ldlf2Automaton(declare, regExpLDLf, ps);
//        ldlA = new LDLfttFormula();
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlA = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // [true]ff
//        regExp = new RegExpLocalTrue();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = AutomatonUtils.ldlf2Automaton(declare, regExpLDLf, ps);
//        ldlA = new LDLfffFormula();
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlA = new LDLfBoxFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // [false]tt
//        regExp = new RegExpLocalFalse();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = AutomatonUtils.ldlf2Automaton(declare, regExpLDLf, ps);
//        ldlA = new LDLfLocalTrueFormula();
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlA = new LDLfBoxFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());


//        // <true>((<a>(tt)) TeAND (<true>(tt)))
//        // <true>tt
//        regExp = new RegExpLocalTrue();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = AutomatonUtils.ldlf2Automaton(declare, regExpLDLf, ps);
//        ldlA = new LDLfttFormula();
//        right = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        ldlA = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//        // <a>tt
//        regExp2 = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp2);
//        left2 = AutomatonUtils.ldlf2Automaton(declare, regExpLDLf, ps);
//        ldlB = new LDLfttFormula();
//        right2 = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
//        ldlB = new LDLfDiamondFormula(regExp2, ldlB);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp2 = compositionAutomatonFactory(ldlB.getFormulaType(), left2, right2);
//        comp2 = new SinkComplete(comp2.alphabet()).transform(comp2); //NEEDED?
//        comp2 = new Reducer<>().transform(comp2);
//        printComparison(automaton, comp2, ldlB);
//        assertEquals(automaton.toString(), comp2.toString());
//        // (<a>(tt)) TeAND (<true>(tt))
//        ldlA = new LDLfTempAndFormula(ldlA, ldlB);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp3 = compositionAutomatonFactory(ldlA.getFormulaType(), comp, comp2);
//        comp3 = new Reducer<>().transform(comp3);
//        printComparison(automaton, comp3, ldlA);
////        assertEquals(automaton.toString(), comp3.toString()); // Correct but inverted I and T
//        // <true>((<a>(tt)) TeAND (<true>(tt)))
//        ldlB = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp4 = compositionAutomatonFactory(ldlB.getFormulaType(), left, comp3);
//        comp4 = new Reducer<>().transform(comp4);
//        printComparison(automaton, comp4, ldlB);
//        assertEquals(automaton.toString(), comp3.toString()); // Not correct
    }

    @Test
    public void elementaryCompTest() {
        boolean declare = true;
        Automaton automaton;
        Automaton comp;
        Automaton comp2;
        Automaton comp3;
        Automaton comp4;
        Automaton left;
        Automaton right;
        Automaton left2;
        Automaton right2;
        Automaton left3;
        Automaton right3;
        LDLfFormula ldlA;
        LDLfFormula ldlB;
        RegExp regExp;
        RegExp regExp2;
        LDLfFormula regExpLDLf;
        PropositionalSignature ps = generateSignature();
        Proposition a = new Proposition("a");
        Proposition b = new Proposition("b");

//        // true
//        ldlA = new LDLfLocalTrueFormula();
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = getElementaryAutomaton(ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), comp, null);
//        automaton = new Reducer<>().transform(automaton);
////        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // false
//        ldlA = new LDLfLocalFalseFormula();
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = getElementaryAutomaton(ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), comp, null);
//        automaton = new Reducer<>().transform(automaton);
////        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // a
//        ldlA = new LDLfLocalVar(a);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = getElementaryAutomaton(ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), comp, null);
//        automaton = new Reducer<>().transform(automaton);
////        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // !a
//        ldlA = new LDLfLocalVar(a);
//        left = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfLocalNotFormula(ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, null);
//        automaton = new Reducer<>().transform(automaton);
////        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString()); // Not the same, accepts empty trace
//
//        // a && b
//        ldlA = new LDLfLocalVar(a);
//        left = getElementaryAutomaton(ldlA, ps);
//        ldlB = new LDLfLocalVar(b);
//        right = getElementaryAutomaton(ldlB, ps);
//        ldlA = new LDLfLocalAndFormula(ldlA, ldlB);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // a || b
//        ldlA = new LDLfLocalVar(a);
//        left = getElementaryAutomaton(ldlA, ps);
//        ldlB = new LDLfLocalVar(b);
//        right = getElementaryAutomaton(ldlB, ps);
//        ldlA = new LDLfLocalOrFormula(ldlA, ldlB);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString()); // Does not loop in accepting state
//
//        // <true>ff
//        regExp = new RegExpLocalTrue();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        ldlA = new LDLfffFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());

//        // <false>tt
//        regExp = new RegExpLocalFalse();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        ldlA = new LDLfLocalTrueFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // <a>tt
//        regExp = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        ldlA = new LDLfttFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfDiamondFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // [true]ff
//        regExp = new RegExpLocalTrue();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        ldlA = new LDLfffFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfBoxFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
//
//        // [false]tt
//        regExp = new RegExpLocalFalse();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        ldlA = new LDLfLocalTrueFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfBoxFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());


        // <true>((<a>(tt)) TeAND (<true>(tt)))
        // <true>tt
        regExp = new RegExpLocalTrue();
        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
        left = getElementaryAutomaton(regExpLDLf, ps);
        ldlA = new LDLfttFormula();
        right = getElementaryAutomaton(ldlA, ps);
        ldlA = new LDLfDiamondFormula(regExp, ldlA);
        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
        automaton = new Reducer<>().transform(automaton);
        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
        comp = new Reducer<>().transform(comp);
        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
        // <a>tt
        regExp2 = new RegExpLocalVar(a);
        regExpLDLf = regExpAtomicLocal2LDLf(regExp2);
        left2 = getElementaryAutomaton(regExpLDLf, ps);
        ldlB = new LDLfttFormula();
        right2 = getElementaryAutomaton(ldlB, ps);
        ldlB = new LDLfDiamondFormula(regExp2, ldlB);
        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
        automaton = new Reducer<>().transform(automaton);
        comp2 = compositionAutomatonFactory(ldlB.getFormulaType(), left2, right2);
//        comp2 = new SinkComplete(comp2.alphabet()).transform(comp2); //NEEDED?
        comp2 = new Reducer<>().transform(comp2);
        printComparison(automaton, comp2, ldlB);
//        assertEquals(automaton.toString(), comp2.toString());
        // (<a>(tt)) TeAND (<true>(tt))
        ldlA = new LDLfTempAndFormula(ldlA, ldlB);
        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
        automaton = new Reducer<>().transform(automaton);
        comp3 = compositionAutomatonFactory(ldlA.getFormulaType(), comp, comp2);
        comp3 = new Reducer<>().transform(comp3);
        printComparison(automaton, comp3, ldlA);
//        assertEquals(automaton.toString(), comp3.toString()); // Correct but inverted I and T
        // <true>((<a>(tt)) TeAND (<true>(tt)))
        ldlB = new LDLfDiamondFormula(regExp, ldlA);
        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
        automaton = new Reducer<>().transform(automaton);
        comp4 = compositionAutomatonFactory(ldlB.getFormulaType(), left, comp3);
        comp4 = new Reducer<>().transform(comp4);
        printComparison(automaton, comp4, ldlB);
//        assertEquals(automaton.toString(), comp3.toString()); // Not correct
    }

    private void printComparison(Automaton automaton, Automaton comp, LDLfFormula formula) {
        System.out.println("Formula: " + formula + "\n");

        System.out.println("LDLf2DFA:");
        System.out.println(automaton.toString());
        System.out.println("------------------------\n");

        System.out.println("Compositional:");
        System.out.println(comp.toString());
        System.out.println("------------------------\n");
    }

    @Test
    public void LDLfToAutomatonTest() {
        boolean declare = true;
        PropositionalSignature ps = generateSignature();
        //input: atomic, atomic regexp, localVar regexp

//        formulaToCompareAutomatons(stringToLDLf("true"), declare, ps);
//
//        formulaToCompareAutomatons(stringToLDLf("False"), declare, ps);

        formulaToCompareAutomatons(stringToLDLf("a"), declare, ps);

//        formulaToCompareAutomatons(stringToLDLf("!a"), declare, ps);
//
//        formulaToCompareAutomatons(stringToLDLf("a && b"), declare, ps);
//
//        stringToAutomaton("a || b", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("a -> b", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("X(a)", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("F(a)", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("G(a)", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("a U b", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("a W b", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("a R b", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("a <-> b", declare, ps);
//        System.out.println("------------------------\n");
//
//        stringToAutomaton("last", declare, ps);
//        System.out.println("------------------------\n");
    }

    private void formulaToCompareAutomatons(LDLfFormula formula, boolean declare, PropositionalSignature ps) {
        System.out.println("Formula: " + formula);

        Automaton automaton;
        automaton = LDLfToAutomaton(declare, formula, ps);
        System.out.println("Compositional:");
        System.out.println(automaton.toString());
        System.out.println("------------------------\n");

        automaton = AutomatonUtils.ldlf2Automaton(declare, formula, ps);
        automaton = new Reducer().transform(automaton);
        System.out.println("LDLf2DFA reduced:");
        System.out.println(automaton.toString());
        System.out.println("------------------------\n");
    }

//    private Automaton getElementalAutomaton(Formula formula, PropositionalSignature ps) {
//        switch (formula.getFormulaType()) {
//            case LDLf_tt -> { return getElementalTt(ps); }
//            case LDLf_ff -> { return getElementalFf(ps); }
////            case LDLf_LOCAL_VAR -> { return getElementalLocalVar(ps, (LDLfFormula) formula); }
////            case RE_LOCAL_VAR -> { return getElementalRegExpLocalVar(ps, (RegExpLocalVar) formula); }
//            default -> {
//                return new Automaton();//throw new RuntimeException("Not implemented yet: " + formula);
//            }
//        }
//    }

    private Automaton getElementalDiamondAutomaton(Automaton regExp, Automaton phi) {
        Automaton automaton;

//        //if regexp is empty (has no terminal state)
//        if (new isEmpty<>().test(regExp)) {
//            //extend regexp with a terminal state using empty trace as label
//            QuotedFormulaStateFactory formulaStateFactory = (QuotedFormulaStateFactory) regExp.getStateFactory();
//            QuotedFormulaState endState = (QuotedFormulaState) formulaStateFactory.create(false, true, new HashSet<>()); //use initial state's formula set??
//            Set<QuotedFormulaState> initialStateSet = regExp.initials();
//            if (initialStateSet.size() != 1) {
//                throw new IllegalArgumentException("Not enough/too many initial states: " + regExp);
//            }
//            Iterator<QuotedFormulaState> it = initialStateSet.iterator();
//            QuotedFormulaState initialState = it.next();
//            Transition<TransitionLabel> t = new Transition<>(initialState, null, endState);
//            try {
//                regExp.addTransition(t);
//            } catch (NoSuchStateException e) {
//                e.printStackTrace();
//            }
            //add all labels to terminal state
//
//        }

        automaton = new MyConcatenation<>().transform(regExp, phi);

        return automaton;
    }

    private Automaton getElementaryAutomaton(LDLfFormula formula, PropositionalSignature ps) {
        Automaton automaton;
        State initialState;
        State endState;
        State falseState;

        automaton = new Automaton();

        Set<PossibleWorld> labels = new HashSet<>();

        for (Proposition p : ps) {
            Set<Proposition> propSet = new HashSet<>();
            propSet.add(p);
            labels.add(new PossibleWorld(propSet));
        }

        if (formula instanceof LDLfttFormula) {
            initialState = automaton.addState(true, true);
            addLoopingTransitions(labels, initialState, initialState, automaton);
        } else if (formula instanceof LDLfffFormula) {
            initialState = automaton.addState(true, false);
            addLoopingTransitions(labels, initialState, initialState, automaton);
        } else {
            initialState = automaton.addState(true, false);
            endState = automaton.addState(false, true);
            falseState = automaton.addState(false, false);

            PropositionalFormula propFormula = ((LDLfLocalFormula) formula).LDLfLocal2Prop();

            for (PossibleWorld label : labels) {
                Transition transition;
                if (label.satisfies(propFormula)) {
                    transition = new Transition(initialState, label, endState);
                } else {
                    transition = new Transition(initialState, label, falseState);
                }

                try {
                    automaton.addTransition(transition);
                } catch (NoSuchStateException e) {
                    e.printStackTrace();
                }
            }

            /*
            Hack, if endState is unreachable set to false
             */
            if (!automaton.accessibleStates().contains(endState)) {
                endState.setTerminal(false);
            }

            addLoopingTransitions(labels, falseState, falseState, automaton);
        }

        return automaton;
    }

    private void addLoopingTransitions(Set<PossibleWorld> labels, State from, State to, Automaton automaton) {
        for (PossibleWorld label : labels) {
            Transition transition;
            transition = new Transition(from, label, to);

            try {
                automaton.addTransition(transition);
            } catch (NoSuchStateException e) {
                e.printStackTrace();
            }
        }
    }

//    private Automaton getElementalRegExpLocalVar(PropositionalSignature ps, RegExpLocalVar formula) {
//        QuotedFormulaStateFactory stateFactory = new QuotedFormulaStateFactory();
//        Automaton automaton = new Automaton(stateFactory);
//        stateFactory.setAutomaton(automaton);
//
//        Set<TransitionLabel> allLabels = AutomatonUtils.buildAllLables(true, ps);
//
//        Set<QuotedVar> initialStateFormulas = new HashSet<>();
//        Set<QuotedVar> endStateFormulas = new HashSet<>();
//
//        endStateFormulas.add(new QuotedVar(new LDLfLocalFalseFormula()));
//
//        /*
//        Translate RegExp to LDLf
//         */
////        QuotedVar quotedVar = new QuotedVar(new LDLfLocalVar(formula.getProp()));
//
//        /*
//        RegExp DFA has 3 states.
//        For labels that satisfy the propositional formula, transition to endState, else to falseState.
//         */
//        QuotedFormulaState initialState = (QuotedFormulaState) stateFactory.create(true, false, initialStateFormulas);
//        QuotedFormulaState falseState = (QuotedFormulaState) stateFactory.create(false, false, new HashSet<>()); //should hold all that does not satisfy prop
//        QuotedFormulaState endState = (QuotedFormulaState) stateFactory.create(false, true, endStateFormulas);
//
//        Transition<TransitionLabel> toFalse = new Transition<>(initialState, new EmptyTrace(), endState);
//
//
//        for (TransitionLabel l : allLabels) {
//            PossibleWorldWrap pw = (PossibleWorldWrap) l;
//            Transition<TransitionLabel> t;
//
//            if (pw.satisfies(formula.regExpLocal2Propositional())) {
//                t = new Transition<>(initialState, pw, endState);
//            } else {
//                t = new Transition<>(initialState, pw, falseState);
//            }
//
//            try {
//                automaton.addTransition(t);
//            } catch (NoSuchStateException e) {
//                e.printStackTrace();
//            }
//        }
//
//        addAllLoopingTransitions(allLabels, automaton, falseState);
//
////        initialStateFormulas.add(quotedVar);
//        /*
//        Create emptyTrace special label (why?)
//         */
////        TransitionLabel emptyTrace = new EmptyTrace();
////        QuotedFormula currentFormula = initialState.getQuotedConjunction();
////        QuotedFormula deltaResult = currentFormula.delta(emptyTrace);
////        Set<Set<QuotedVar>> allMinimalModels = deltaResult.getMinimalModels();
////
////        if (allMinimalModels.isEmpty()) {
////            // The false state (?)
////        }
//
//
//
//        return automaton;
//    }

//    private Automaton getElementalLocalVar(PropositionalSignature ps, LDLfFormula formula) {
//        Automaton automaton = new Automaton();
//        State initialState = automaton.addState(true, false);
//        Set<PossibleWorld> models = propFormula.getModels();
//        for (PossibleWorld p : models) {
//            try {
//                automaton.addTransition(new Transition(initialState, p, initialState));
//            } catch (NoSuchStateException e) {
//                System.err.println(e.toString());
//            }
//        }
//        return automaton;
//    }

//    private Automaton getElementalFf(PropositionalSignature ps) {
//        QuotedFormulaStateFactory stateFactory = new QuotedFormulaStateFactory();
//        Automaton automaton = new Automaton(stateFactory);
//        stateFactory.setAutomaton(automaton);
//
//        Set<TransitionLabel> allLabels = AutomatonUtils.buildAllLables(true, ps);
//        Set<QuotedVar> initialStateFormulas = new HashSet<>();
//
//        /*
//        Only one state in elemental ff automaton, it is initial but not terminal.
//         */
//        QuotedFormulaState initialState = (QuotedFormulaState) stateFactory.create(true, false, initialStateFormulas);
//
//        addAllLoopingTransitions(allLabels, automaton, initialState);
//
//        return automaton;
//    }

//    private Automaton getElementalTt(PropositionalSignature ps) {
//        QuotedFormulaStateFactory stateFactory = new QuotedFormulaStateFactory();
//        Automaton automaton = new Automaton(stateFactory);
//        stateFactory.setAutomaton(automaton);
//
//        Set<TransitionLabel> allLabels = AutomatonUtils.buildAllLables(true, ps);
//
//        /*
//        Empty set of quoted formulas in elemental tt automaton
//         */
//        Set<QuotedVar> initialStateFormulas = new HashSet<>();
//
//        /*
//        Only one state in elemental tt automaton, it is both initial and terminal.
//         */
//        QuotedFormulaStateFactory.QuotedFormulaState initialState = (QuotedFormulaStateFactory.QuotedFormulaState) stateFactory.create(true, true, initialStateFormulas);
//
//        addAllLoopingTransitions(allLabels, automaton, initialState);
//
//        return automaton;
//    }

//    private void addAllLoopingTransitions(Set<TransitionLabel> allLabels, Automaton automaton, QuotedFormulaStateFactory.QuotedFormulaState toState) {
//        /*
//        Add all looping transitions
//         */
//        for (TransitionLabel label : allLabels) {
//            Transition<TransitionLabel> transition = new Transition<>(toState, label, toState);
//            try {
//                automaton.addTransition(transition);
//            } catch (NoSuchStateException e) {
//                e.printStackTrace();
//            }
//        }
//    }

    private LDLfFormula stringToLDLf(String input) {
        LTLfFormula ltl = parseLTLfFormula(input);
        LDLfFormula ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        return ldl;
    }

    private PropositionalSignature generateSignature() {
        PropositionalSignature ps = new PropositionalSignature();

        Proposition a = new Proposition("a");
        Proposition b = new Proposition("b");
//        Proposition last = new PropositionLast();

        ps.add(a);
        ps.add(b);
//        ps.add(last);

        return ps;
    }

    @Test
    public void stringParserTest() {
        boolean declare = true;
        Automaton automaton;
        PropositionalSignature ps = generateSignature();

        stringToAutomaton("a", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("true", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("False", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("!a", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("a && b", declare, ps);
        System.out.println("------------------------\n");

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempAndFormula(ltlA, ltlB);
        System.out.println("ltl: " + ltl);
        ldlA = ltl.toLDLf();
        System.out.println("ldl: " + ldlA);
        ldlA = (LDLfFormula) ldlA.nnf();
        System.out.println("nnf: " + ldlA);
        automaton = LDLfToAutomaton(declare, ldlA, ps);
        assertNotNull(automaton);
        System.out.println("------------------------\n");

        stringToAutomaton("a || b", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("a -> b", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("X(a)", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("F(a)", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("G(a)", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("a U b", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("a W b", declare, ps);
        System.out.println("------------------------\n");

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfWeakUntilFormula(ltlA, ltlB);
        System.out.println("ltl: " + ltl);
        ldlA = ltl.toLDLf();
        System.out.println("ldl: " + ldlA);
        ldlA = (LDLfFormula) ldlA.nnf();
        System.out.println("nnf: " + ldlA);
        automaton = LDLfToAutomaton(declare, ldlA, ps);
        assertNotNull(automaton);
        System.out.println("------------------------\n");

        stringToAutomaton("a R b", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("a <-> b", declare, ps);
        System.out.println("------------------------\n");

        stringToAutomaton("last", declare, ps);
        System.out.println("------------------------\n");
    }

    private void stringToAutomaton(String input, boolean declare, PropositionalSignature ps) {
        //1. parse input string to LTLfFormula
        ltl = parseLTLfFormula(input);
        System.out.println("ltl: " + ltl);

        //2. convert LTLfFormula to LDLfFormula
        ldlA = ltl.toLDLf();
        System.out.println("ldl: " + ldlA);

        //3. convert to normal negated form(?)
        ldlA = (LDLfFormula) ldlA.nnf();
        System.out.println("nnf: " + ldlA);

        //4. parse LDLfFormula
        Automaton automaton = LDLfToAutomaton(declare, ldlA, ps);
        assertNotNull(automaton);
    }

    private Automaton LDLfToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps) {
        Automaton automaton;

        /*
        * Base case when the formula is an atomic proposition
        */
        if (formula instanceof AtomicFormula) {
//            System.out.println("atomic: " + formula + " type: " +formula.getFormulaType());
//            if (formula.getFormulaType() == FormulaType.LDLf_tt) {
//                automaton = getElementalTt(ps);
//            } else {
//                automaton = AutomatonUtils.ldlf2Automaton(declare, formula, ps);
            automaton = getElementaryAutomaton(formula, ps);
//                automaton = new Reducer<>().transform(automaton);
//                System.out.println("ldlf atomic: " + automaton);
//                return getElementalAutomaton(formula, ps);
//            }
            automaton = compositionAutomatonFactory(formula.getFormulaType(), automaton, null);
            return automaton;
        }

        /* Else parse subformula */
        if (formula instanceof UnaryFormula) {
            UnaryFormula uFormula = (UnaryFormula) formula;
            LDLfFormula nested = (LDLfFormula) uFormula.getNestedFormula();
            automaton = LDLfToAutomaton(declare, nested, ps);
            automaton = compositionAutomatonFactory(formula.getFormulaType(), automaton, null);
        } else if (formula instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) formula;
            LDLfFormula left = (LDLfFormula) bFormula.getLeftFormula();
            LDLfFormula right = (LDLfFormula) bFormula.getRightFormula();
            Automaton leftAutomaton = LDLfToAutomaton(declare, left, ps);
            Automaton rightAutomaton = LDLfToAutomaton(declare, right, ps);
//            automaton = concatWrapper(leftAutomaton, rightAutomaton);
            automaton = compositionAutomatonFactory(formula.getFormulaType(), leftAutomaton, rightAutomaton);
        } else if (formula instanceof TemporalFormula) {
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) formula;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();
            Automaton regAutomaton = regexpToAutomaton(declare, reg, ps);
            Automaton goalAutomaton = LDLfToAutomaton(declare, goal, ps);
//            automaton = concatWrapper(regAutomaton, goalAutomaton);
            automaton = compositionAutomatonFactory(formula.getFormulaType(), regAutomaton, goalAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal formula " + formula);
        }

        //perform automata operations on DFA returned from subformula

        return automaton;
    }

    private Automaton regexpToAutomaton(boolean declare, RegExp regExp, PropositionalSignature ps) {
        Automaton automaton;

        /* Base case when expression is atomic proposition */
        if (regExp instanceof AtomicFormula || regExp instanceof LocalFormula) { //RE_LOCAL_VAR, RE_LOCAL_TRUE, RE_LOCAL__FALSE
//            System.out.println("atomic regexp: " + regExp + " type: " + regExp.getFormulaType());
            LDLfFormula ldlfFormula = regExpAtomicLocal2LDLf(regExp);
//            automaton = AutomatonUtils.ldlf2Automaton(declare, ldlfFormula, ps);
            automaton = LDLfToAutomaton(declare, ldlfFormula, ps);
            automaton = compositionAutomatonFactory(FormulaType.LDLf_LOCAL_VAR, automaton, null);
            return automaton;
        }

        /* Else parse subformula */
        if (regExp instanceof UnaryFormula) {
            UnaryFormula uFormula = (UnaryFormula) regExp;
            Formula nested = uFormula.getNestedFormula();
            if (nested instanceof RegExp) {
                automaton = regexpToAutomaton(declare, (RegExp) nested, ps);
            } else if (nested instanceof LDLfFormula) {
                automaton = LDLfToAutomaton(declare, (LDLfFormula) nested, ps); //Special case (RegExpTest)
            } else {
                throw new IllegalArgumentException("Nested formula of unknown type " + nested.getClass());
            }
            automaton = compositionAutomatonFactory(regExp.getFormulaType(), automaton, null);
        } else if (regExp instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) regExp;
            RegExp left = (RegExp) bFormula.getLeftFormula(); //Can be LDLfFormula?
            RegExp right = (RegExp) bFormula.getRightFormula(); //Can be LDLfFormula?
            Automaton leftAutomaton = regexpToAutomaton(declare, left, ps);
            Automaton rightAutomaton = regexpToAutomaton(declare, right, ps);
//            automaton = concatWrapper(leftAutomaton, rightAutomaton);
            automaton = compositionAutomatonFactory(regExp.getFormulaType(), leftAutomaton, rightAutomaton);
        } else if (regExp instanceof TemporalFormula) {
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) regExp;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();
            Automaton regAutomaton = regexpToAutomaton(declare, reg, ps);
            Automaton goalAutomaton = LDLfToAutomaton(declare, goal, ps);
//            automaton = concatWrapper(regAutomaton, goalAutomaton);
            automaton = compositionAutomatonFactory(regExp.getFormulaType(), regAutomaton, goalAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal regexp " + regExp);
        }

        return automaton;
    }

    private Automaton compositionAutomatonFactory(FormulaType type, Automaton left, Automaton right) {
        Automaton compAutomaton;
        Automaton notEpsilon;

        switch (type) {
            case LDLf_LOCAL_TRUE:
//                compAutomaton = getElementalTt(generateSignature());
//                break;
            case LDLf_tt:
            case LDLf_LOCAL_FALSE:
            case LDLf_ff:
            case LDLf_LOCAL_VAR:
                compAutomaton = left;
                break;
            case LDLf_LOCAL_NOT:
                /*
                To avoid accepting the empty trace
                 */
                Set<State> statesSet = left.states();
                for (State s : statesSet) {
                    if (s.isInitial()) {
                        s.setTerminal(true);
                    }
                }
//                notEpsilon = AutomatonUtils.ldlf2Automaton(true, new LDLfLocalTrueFormula(), generateSignature());
//                notEpsilon = getElementaryAutomaton(new LDLfLocalTrueFormula(), generateSignature());
//                Automaton epsilon = new Automaton();
//                Automaton epsilon = Automaton.epsilonAutomaton();
//                Automaton epsilon = getElementaryAutomaton(new LDLfLocalTrueFormula(), generateSignature());
//                epsilon = new CompleteNop<>(left.alphabet()).transform(epsilon);
//                compAutomaton = new Union<>().transform(epsilon, left);
//                compAutomaton = new Concatenation<>().transform(epsilon, left);
//                compAutomaton = new EpsilonTransitionRemover<>().transform(compAutomaton);
//                compAutomaton = new Mix<>().transform(epsilon, left);
//                compAutomaton = new EpsilonTransitionRemover<>().transform(compAutomaton);
                compAutomaton = new Complement<>().transform(left);
//                compAutomaton = new Union<>().transform(epsilon, compAutomaton);
//                compAutomaton = new Normalizer<>().transform(compAutomaton);
//                compAutomaton = new Concatenation<>().transform(epsilon, compAutomaton);
//                compAutomaton = new Mix<>().transform(epsilon, compAutomaton);
//                compAutomaton = new EpsilonTransitionRemover<>().transform(compAutomaton);
//                compAutomaton = new Concatenation<>().transform(notEpsilon, compAutomaton);
//                compAutomaton = new EpsilonTransitionRemover<>().transform(compAutomaton);
                break;
            case LDLf_LOCAL_AND:
//                compAutomaton = new Mix<>().transform(left, right);
//                break;
            case LDLf_TEMP_AND:
                compAutomaton = new Mix<>().transform(left, right);
                break;
            case LDLf_LOCAL_OR:
//                compAutomaton = new Union<>().transform(left, right);
//                break;
            case LDLf_TEMP_OR:
                compAutomaton = new Union<>().transform(left, right);
                break;
            case LDLf_BOX:
//                left = new Reducer<>().transform(left);
                Automaton complement = new Complement<>().transform(left);
//                compAutomaton = new MyConcatenation<>().transform(left, right);
                compAutomaton = new Concatenation<>().transform(left, right);
//                compAutomaton = new MyConcatenation<>().transform(complement, compAutomaton);
                compAutomaton = new Union<>().transform(complement, compAutomaton);
                break;
            case LDLf_DIAMOND:
//                notEpsilon = AutomatonUtils.ldlf2Automaton(true, new LDLfLocalTrueFormula(), generateSignature());
//                left = new MyConcatenation<>().transform(notEpsilon, left);
//                Automaton leftTemp = new Normalizer<>().transform(left);
//                leftTemp = new EpsilonTransitionRemover<>().transform(leftTemp);
//                Automaton rightTemp = new Normalizer<>().transform(right);
//                rightTemp = new EpsilonTransitionRemover<>().transform(rightTemp);
                compAutomaton = new MyConcatenation<>().transform(left, right);
//                compAutomaton = new MyConcatenation<>().transform(leftTemp, rightTemp);
//                compAutomaton = new Concatenation<>().transform(left, right);
//                compAutomaton = new EpsilonTransitionRemover<>().transform(compAutomaton);
//                Set<PossibleWorld> alphabet = left.alphabet();
//                compAutomaton = new CompleteNop<>(alphabet).transform(compAutomaton);
//                compAutomaton = new Concatenation<>().transform(left, right);
//                compAutomaton = new Mix<>().transform(left, compAutomaton);
                break;
            default:
                throw new IllegalArgumentException("Not implemented yet: " + type);

//            LDLf_TEMP_NOT,
//            LDLf_TEMP_IMPL,
//            LDLf_TEMP_DOUBLEIMPL,
//            LDLf_LOCAL_IMPL,
//            LDLf_LOCAL_DOUBLEIMPL,
//                RE_STAR (use LDL2DFA algorithm as in de2021?)
        }
//        compAutomaton = new ToDFA<>().transform(compAutomaton);
//        compAutomaton = new SinkComplete().transform(compAutomaton);
//        compAutomaton = new CompleteNop<>(left.alphabet()).transform(compAutomaton);
//        compAutomaton = new EpsilonTransitionRemover<>().transform(compAutomaton);
//        compAutomaton = new Reducer<>().transform(compAutomaton);

        return compAutomaton;
    }

    private Automaton concatWrapper(Automaton a1, Automaton a2) {
        Automaton automaton = new Concatenation<>().transform(a1, a2);
        automaton = new Reducer<>().transform(automaton);
//            automaton = new SinkComplete().transform(automaton); //Needed?
        return automaton;
    }

    private LDLfFormula regExpAtomicLocal2LDLf(RegExp regExp) {
        LDLfFormula ldlfFormula;

        FormulaType type = regExp.getFormulaType();
        switch (type) {
            case RE_LOCAL_TRUE -> ldlfFormula = new LDLfLocalTrueFormula();
            case RE_LOCAL_FALSE -> ldlfFormula = new LDLfLocalFalseFormula();
            default -> {
                PropositionalFormula propForm = ((RegExpLocal) regExp).regExpLocal2Propositional();
//                System.out.println("prop: " + propForm.toString());
                ldlfFormula = parseLocalFormula(propForm.toString());
//                System.out.println("ldl: " + ldlfFormula);
            }
        }
        return ldlfFormula;
    }

//    private LDLfFormula translateRegExpToLDLf(RegExp regExp) {
//        LDLfFormula ldlfFormula;
//        FormulaType type = regExp.getFormulaType();
//
//        switch (type) {
//            case RE_LOCAL_VAR -> {
//                PropositionalFormula propForm = ((RegExpLocal) regExp).regExpLocal2Propositional();
//                ldlfFormula = parseLocalFormula(propForm.toString());
////                ldlfFormula = new LDLfLocalVar(((RegExpLocalVar) regExp).getProp());
//            }
//            case RE_LOCAL_TRUE -> ldlfFormula = new LDLfLocalTrueFormula();
//            case RE_LOCAL_FALSE -> ldlfFormula = new LDLfLocalFalseFormula();
//            case RE_LOCAL_NOT -> {
////                RegExpLocalNot regExpLocalVar = ((RegExpLocalNot) regExp).regExpLocal2Propositional();
//                PropositionalFormula propFormula = ((RegExpLocal) regExp).regExpLocal2Propositional();
////                Proposition prop = regExpLocalVar.getProp();
////                ldlfFormula = new LDLfLocalVar(prop);
////                ldlfFormula = LDLfLocalFormula.localFormulaFactory(LocalFormulaType.PROP_NOT, (LDLfLocalFormula) ldlfFormula, null, prop);
//                System.out.println("prop: " + propFormula.toString());
//                ldlfFormula = parseLocalFormula(propFormula.toString());
//            }
//            case RE_LOCAL_AND -> {
//                PropositionalFormula propositionalFormula = ((RegExpLocal) regExp).regExpLocal2Propositional();
//                Set<Proposition> propositions = propositionalFormula.getAtoms();
//                Set<PropositionalFormula> propositionalFormulas = propositionalFormula.getLiterals();
//                ldlfFormula = null;
//            }
//
//            default -> throw new IllegalArgumentException("Not implemented yet: " + type);
//        }
//        return ldlfFormula;
//    }

    @Test
    public void LDLfToNnfTest() {
        //3. convert to normal negated form(?)
        ltl = parseLTLfFormula("a");
        ldlA = ltl.toLDLf();
        ldlA = (LDLfFormula) ldlA.nnf();
        assertEquals("<a>(tt)", ldlA.toString());

        ltl = parseLTLfFormula("a");
        ltl = new LTLfTempNotFormula(ltl);
        ldlA = ltl.toLDLf();
        ldlA = (LDLfFormula) ldlA.nnf();
        assertEquals("[a](ff)", ldlA.toString());

        ltl = parseLTLfFormula("last");
        ldlA = ltl.toLDLf();
        ldlA = (LDLfFormula) ldlA.nnf();
        assertEquals("[true](([true](ff)) TeOR ([true](ff)))", ldlA.toString());
    }

    @Test
    public void LTLfToLDLfTest() {
        //2. convert LTLfFormula to LDLfFormula
        ltlA = parseLTLfFormula("a");
        ldlA = ltlA.toLDLf();
        assertEquals("<a>(tt)", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfTempNotFormula(ltlA);
        ldlA = ltlA.toLDLf();
        assertEquals("TeNOT(<a>(tt))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempAndFormula(ltlA, ltlB);
        ldlA = ltl.toLDLf();
        assertEquals("(<a>(tt)) TeAND (<b>(tt))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempOrFormula(ltlA, ltlB);
        ldlA = ltl.toLDLf();
        assertEquals("(<a>(tt)) TeOR (<b>(tt))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempImplFormula(ltlA, ltlB);
        ldlA = ltl.toLDLf();
        assertEquals("(NOT(<a>(tt))) TeOR (<b>(tt))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfNextFormula(ltlA);
        ldlA = ltlA.toLDLf();
        assertEquals("<true>((<a>(tt)) TeAND (TeNOT([true](ff))))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfEventuallyFormula(ltlA);
        ldlA = ltlA.toLDLf();
        assertEquals("<*(true)>((<a>(tt)) TeAND (TeNOT([true](ff))))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlA = new LTLfGloballyFormula(ltlA);
        ldlA = ltlA.toLDLf();
        assertEquals("TeNOT(<*(true)>((<NOT(a)>(tt)) TeAND (TeNOT([true](ff)))))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfUntilFormula(ltlA, ltlB);
        ldlA = ltl.toLDLf();
        assertEquals("<*((?(<a>(tt))) ; (true))>((<b>(tt)) TeAND (TeNOT([true](ff))))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfWeakUntilFormula(ltlA, ltlB);
        ldlA = ltl.toLDLf();
        assertEquals("(<*((?(<a>(tt))) ; (true))>((<b>(tt)) TeAND (TeNOT([true](ff))))) TeOR (TeNOT(<*(true)>((<NOT(a)>(tt)) TeAND (TeNOT([true](ff))))))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfReleaseFormula(ltlA, ltlB);
        ldlA = ltl.toLDLf();
        assertEquals("TeNOT(<*((?(<NOT(a)>(tt))) ; (true))>((<NOT(b)>(tt)) TeAND (TeNOT([true](ff)))))", ldlA.toString());

        ltlA = parseLTLfFormula("a");
        ltlB = parseLTLfFormula("b");
        ltl = new LTLfTempDoubleImplFormula(ltlA, ltlB);
        ldlA = ltl.toLDLf();
        assertEquals("((NOT(<a>(tt))) TeOR (<b>(tt))) TeAND ((NOT(<b>(tt))) TeOR (<a>(tt)))", ldlA.toString());

        ltlA = parseLTLfFormula("last");
        ltl = ltlA;
        ldlA = ltl.toLDLf();
        assertEquals("TeNOT(<true>((<true>(tt)) TeAND (TeNOT([true](ff)))))", ldlA.toString());

        ltlA = parseLTLfFormula("true");
        ltl = ltlA;
        ldlA = ltl.toLDLf();
        assertEquals("<true>(tt)", ldlA.toString());

        ltlA = parseLTLfFormula("False");
        ltl = ltlA;
        ldlA = ltl.toLDLf();
        assertEquals("<false>(tt)", ldlA.toString());
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

    private LDLfLocalFormula parseLocalFormula(String input) {
        LDLfLocalFormula output;

        PropFormulaParserLexer lexer = new PropFormulaParserLexer(new ANTLRInputStream(input));
        PropFormulaParserParser parser = new PropFormulaParserParser(new CommonTokenStream(lexer));
        ParseTree tree = parser.propositionalFormula();
        LocalVisitor<LDLfLocalFormula> implementation = new LocalVisitor(LDLfLocalFormula.class);
        output = implementation.visit(tree);

        return output;
    }
}