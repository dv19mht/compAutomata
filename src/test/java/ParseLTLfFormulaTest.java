import antlr4_generated.LTLfFormulaParserLexer;
import antlr4_generated.LTLfFormulaParserParser;
import antlr4_generated.PropFormulaParserLexer;
import antlr4_generated.PropFormulaParserParser;
import compositionalUtils.MyConcatenation;
import formula.*;
import formula.ldlf.*;
import formula.ltlf.*;
import formula.regExp.*;
import net.sf.tweety.logics.pl.semantics.PossibleWorld;
import net.sf.tweety.logics.pl.syntax.*;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.Test;
import rationals.*;
import rationals.transformations.*;
//import rationals.transformations.MyConcatenation;
import utils.AutomatonUtils;
import visitors.LTLfVisitors.LTLfVisitor;
import visitors.PropVisitor.LocalVisitor;

import java.util.HashSet;
import java.util.Set;

import static org.junit.Assert.*;

public class ParseLTLfFormulaTest {
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
    String strEnd = "end";

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
//
//        ldlA = stringToLDLf(strNotA);
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strAandB); //Unsatisfiable regexp when declare is true (a && b can not be true at the same time).
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strAorB);
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strAimplB);
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strNextA);
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strEventuallyA);
//        createAutomataPrintResults(ldlA);
//
        ldlA = stringToLDLf(strGlobalA); //Not correct
        createAutomataPrintResults(ldlA);

//        ldlA = stringToLDLf(strAuntilB); //RE_TEST not implemented yet
//        createAutomataPrintResults(ldlA);
//        Automaton automaton = AutomatonUtils.ldlf2Automaton(true, ldlA, generateSignature());
//        automaton = new Reducer<>().transform(automaton);
//        System.out.println("Formula: " + ldlA);
//        System.out.println(automaton);

//        ldlA = stringToLDLf(strAweakUntilB); //RE_TEST not implemented yet
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strAreleaseB); //RE_TEST not implemented yet
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strAdoubleImpB);
//        createAutomataPrintResults(ldlA);
//
//        ldlA = stringToLDLf(strLast);
//        createAutomataPrintResults(ldlA);

//        ldlA = getEndFormula();
//        createAutomataPrintResults(ldlA);
    }

    private void createAutomataPrintResults(LDLfFormula formula) {
        Automaton automaton;
        Automaton comp;
        boolean declare = true;
        PropositionalSignature ps = generateSignature();

        automaton = AutomatonUtils.ldlf2Automaton(declare, formula, ps);
        automaton = new Reducer<>().transform(automaton);

        comp = LDLfToAutomaton(declare, formula, ps);
        comp = new Reducer<>().transform(comp);

//        comp = new CompleteNop<>(comp.alphabet()).transform(comp);
        comp = new SinkComplete().transform(comp);

        printComparison(automaton, comp, formula);

//        ModelCheck model = new ModelCheck<>();
//        boolean equal = model.test(automaton, comp);
//        System.out.println("Is equal: " + (equal? "true" : "FALSE"));
//        if (!equal) {
//            System.out.println(model.counterExamples().toString());
//        }
//        System.out.println("------------------------\n");

//        Simulation simulation = new Simulation(automaton, comp);
//        boolean equal = simulation.equivalence(automaton.states(), comp.states());
//        System.out.println(equal);

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
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // false
//        ldlA = new LDLfLocalFalseFormula();
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = getElementaryAutomaton(ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), comp, null);
//        automaton = new Reducer<>().transform(automaton);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // a
//        ldlA = new LDLfLocalVar(a);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        comp = getElementaryAutomaton(ldlA, ps);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), comp, null);
//        automaton = new Reducer<>().transform(automaton);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
        // !a
        ldlA = new LDLfLocalVar(a);
//        left = getElementaryAutomaton(ldlA, ps);
        ldlA = new LDLfLocalNotFormula(ldlA);
        left = getElementaryAutomaton(ldlA, ps);
        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, null);
        automaton = new Reducer<>().transform(automaton);
        comp = new Reducer<>().transform(comp);
        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString()); // Not the same, accepts empty trace

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
//
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
////        assertEquals(automaton.toString(), comp.toString());
//
//        // [false]tt
//        regExp = new RegExpLocalFalse();
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        ldlA = new LDLfttFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfBoxFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());

//        // [a]ff
//        regExp = new RegExpLocalVar(a);
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
////        assertEquals(automaton.toString(), comp.toString());
//
//        // [*(a)]ff
//        regExp = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        regExp = new RegExpStar(regExp);
//        right = LDLfToAutomaton(declare, getEndFormula(), ps);
//        left = compositionAutomatonFactory(regExp.getFormulaType(), left, right);
//        ldlA = new LDLfffFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfBoxFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());
//
//        // [*(true)](([NOT(a)](ff)) TeOR ([true](ff)))
//        // [NOT(a)](ff)
//        regExp = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        comp = LDLfToAutomaton(declare, regExpLDLf, ps);
//        regExp2 = new RegExpLocalNot(regExp);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp2);
//        comp = compositionAutomatonFactory(regExpLDLf.getFormulaType(), comp, null);
//        ldlA = new LDLfffFormula();
//        comp2 = LDLfToAutomaton(declare, ldlA, ps);
//        ldlB = new LDLfBoxFormula(regExp2, ldlA);
//        comp3 = compositionAutomatonFactory(ldlB.getFormulaType(), comp, comp2);
//        comp3 = new Reducer<>().transform(comp3);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
//        automaton = new Reducer<>().transform(automaton);
//        printComparison(automaton, comp3, ldlB);
//        // [*(true)]([NOT(a)](ff))
////        regExp = new RegExpLocalTrue();
//        // [*(a)]([NOT(a)](ff))
//        regExp = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        comp = getElementaryAutomaton(regExpLDLf, ps);
//        regExp = new RegExpStar(regExp);
//        right = LDLfToAutomaton(declare, getEndFormula(), ps);
//        comp = compositionAutomatonFactory(regExp.getFormulaType(), comp, right);
//        ldlA = new LDLfBoxFormula(regExp, ldlB);
//        comp2 = compositionAutomatonFactory(ldlA.getFormulaType(), comp, comp3);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp2 = new Reducer<>().transform(comp2);
//        printComparison(automaton, comp2, ldlA);

//        // <true>((<a>(tt)) TeAND (<true>(tt)))
//        // <true>tt
//        regExp = new RegExpLocalTrue();
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
//        // <a>tt
//        regExp2 = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp2);
//        left2 = getElementaryAutomaton(regExpLDLf, ps);
//        ldlB = new LDLfttFormula();
//        right2 = getElementaryAutomaton(ldlB, ps);
//        ldlB = new LDLfDiamondFormula(regExp2, ldlB);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlB, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp2 = compositionAutomatonFactory(ldlB.getFormulaType(), left2, right2);
//        comp2 = new Reducer<>().transform(comp2);
//        printComparison(automaton, comp2, ldlB);
////        assertEquals(automaton.toString(), comp2.toString());
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
////        assertEquals(automaton.toString(), comp3.toString()); // Not correct
    }

    @Test
    public void elementaryCompTest2() {
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

//        // [*(a)]ff
//        regExp = new RegExpLocalVar(a);
//        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
//        left = getElementaryAutomaton(regExpLDLf, ps);
//        regExp = new RegExpStar(regExp);
//        right = LDLfToAutomaton(declare, getEndFormula(), ps);
//        left = compositionAutomatonFactory(regExp.getFormulaType(), left, right);
//        ldlA = new LDLfffFormula();
//        right = getElementaryAutomaton(ldlA, ps);
//        ldlA = new LDLfBoxFormula(regExp, ldlA);
//        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
//        automaton = new Reducer<>().transform(automaton);
//        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
//        comp = new Reducer<>().transform(comp);
//        printComparison(automaton, comp, ldlA);
////        assertEquals(automaton.toString(), comp.toString());

        // [*(true)](a)
        regExp = new RegExpLocalTrue();
        regExpLDLf = regExpAtomicLocal2LDLf(regExp);
        left = getElementaryAutomaton(regExpLDLf, ps);
        regExp = new RegExpStar(regExp);
        right = LDLfToAutomaton(declare, getEndFormula(), ps);
        left = compositionAutomatonFactory(regExp.getFormulaType(), left, right);
        ldlA = new LDLfLocalVar(a);
        right = getElementaryAutomaton(ldlA, ps);
        ldlA = new LDLfBoxFormula(regExp, ldlA);
        automaton = AutomatonUtils.ldlf2Automaton(declare, ldlA, ps);
        automaton = new Reducer<>().transform(automaton);
        comp = compositionAutomatonFactory(ldlA.getFormulaType(), left, right);
        comp = new Reducer<>().transform(comp);
        printComparison(automaton, comp, ldlA);
//        assertEquals(automaton.toString(), comp.toString());
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
//            try {
//                automaton.addTransition(new Transition<PossibleWorld>(initialState, null, initialState));
//            } catch (NoSuchStateException e) {
//                e.printStackTrace();
//            }
            addLoopingTransitions(labels, initialState, initialState, automaton);
        } else if (formula instanceof LDLfffFormula) {
            initialState = automaton.addState(true, false);
//            try {
//                automaton.addTransition(new Transition<PossibleWorld>(initialState, null, initialState));
//            } catch (NoSuchStateException e) {
//                e.printStackTrace();
//            }
            addLoopingTransitions(labels, initialState, initialState, automaton);
        } else {
            if (!(formula instanceof LDLfLocalFormula)) {
                throw new IllegalArgumentException("Formula is not a LDLfLocalFormula: " + formula.getFormulaType());
            }

            initialState = automaton.addState(true, false);
            endState = automaton.addState(false, true);
            falseState = automaton.addState(false, false);

            PropositionalFormula propFormula = ((LDLfLocalFormula) formula).LDLfLocal2Prop();

            for (PossibleWorld label : labels) {
                Transition<PossibleWorld> transition;
                if (label.satisfies(propFormula)) {
                    transition = new Transition<>(initialState, label, endState);
                } else {
                    transition = new Transition<>(initialState, label, falseState);
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

//            addLoopingTransitions(labels, falseState, falseState, automaton);
        }

        automaton = new Reducer<>().transform(automaton);

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
        if (formula instanceof LocalFormula || formula instanceof AtomicFormula) {
//        if (formula instanceof AtomicFormula) {
            automaton = getElementaryAutomaton(formula, ps);
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
            automaton = compositionAutomatonFactory(formula.getFormulaType(), leftAutomaton, rightAutomaton);
        } else if (formula instanceof TemporalFormula) {
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) formula;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();
            Automaton regAutomaton = regexpToAutomaton(declare, reg, ps);
            Automaton goalAutomaton = LDLfToAutomaton(declare, goal, ps);
            automaton = compositionAutomatonFactory(formula.getFormulaType(), regAutomaton, goalAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal formula " + formula);
        }

        return automaton;
    }

    private Automaton regexpToAutomaton(boolean declare, RegExp regExp, PropositionalSignature ps) {
        Automaton automaton;

        /* Base case when expression is atomic proposition */
        if (regExp instanceof AtomicFormula || regExp instanceof LocalFormula) { //RE_LOCAL_VAR, RE_LOCAL_TRUE, RE_LOCAL__FALSE
            LDLfFormula ldlfFormula = regExpAtomicLocal2LDLf(regExp);
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
            } else if (nested instanceof LDLfFormula) { //Special case when RegExpTest
                automaton = LDLfToAutomaton(declare, (LDLfFormula) nested, ps);
            } else {
                throw new IllegalArgumentException("Nested formula of unknown type " + nested.getClass());
            }

            if (regExp instanceof RegExpStar) {
                Automaton end = LDLfToAutomaton(declare, getEndFormula(), ps);
                automaton = compositionAutomatonFactory(regExp.getFormulaType(), automaton, end);
            } else {
                automaton = compositionAutomatonFactory(regExp.getFormulaType(), automaton, null);
            }
        } else if (regExp instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) regExp;
            RegExp left = (RegExp) bFormula.getLeftFormula(); //Can be LDLfFormula?
            RegExp right = (RegExp) bFormula.getRightFormula(); //Can be LDLfFormula?
            Automaton leftAutomaton = regexpToAutomaton(declare, left, ps);
            Automaton rightAutomaton = regexpToAutomaton(declare, right, ps);
            automaton = compositionAutomatonFactory(regExp.getFormulaType(), leftAutomaton, rightAutomaton);
        } else if (regExp instanceof TemporalFormula) {
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) regExp;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();
            Automaton regAutomaton = regexpToAutomaton(declare, reg, ps);
            Automaton goalAutomaton = LDLfToAutomaton(declare, goal, ps);
            automaton = compositionAutomatonFactory(regExp.getFormulaType(), regAutomaton, goalAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal regexp " + regExp);
        }

        return automaton;
    }

    private Automaton compositionAutomatonFactory(FormulaType type, Automaton left, Automaton right) {
        Automaton compAutomaton;

        switch (type) {
            case LDLf_LOCAL_TRUE:
            case LDLf_LOCAL_FALSE:
            case LDLf_LOCAL_VAR:
            case LDLf_LOCAL_NOT:
            case LDLf_LOCAL_AND:
            case LDLf_LOCAL_OR:
            case LDLf_tt:
            case LDLf_ff:
                compAutomaton = left;
                break;
                /*
                To avoid accepting epsilon after complement
                 */
//                compAutomaton = getComplementNotEpsilonAutomaton(left);
//                compAutomaton = new Complement<>().transform(left);
//                break;
//            case LDLf_LOCAL_AND:
            case LDLf_TEMP_AND:
                compAutomaton = new Mix<>().transform(left, right);
                break;
//            case LDLf_LOCAL_OR:
            case LDLf_TEMP_OR:
                compAutomaton = new Union<>().transform(left, right);
                break;
            case LDLf_BOX:
                /* Best options so far */
//                Set<State> stateSet1 = left.states();
//                for (State s : stateSet1) {
//                    s.setTerminal(!s.isTerminal());
//                }
//                Automaton complement = left.clone();
//                compAutomaton = new Union<>().transform(complement, right);
//                compAutomaton = new Reducer<>().transform(compAutomaton);
                /* ----------------- */

                Automaton compRight = new Complement<>().transform(right);
                compAutomaton = new MyConcatenation<>().transform(left, compRight);
                compAutomaton = new Reducer<>().transform(compAutomaton);
                compAutomaton = new Complement<>().transform(compAutomaton);

                break;
            case RE_CONCAT: // More needed?
            case LDLf_DIAMOND:
//                left = new SinkComplete().transform(left);
                compAutomaton = new MyConcatenation<>().transform(left, right);
                break;
//            case RE_TEST:
//                compAutomaton = left;
//                break;
            case RE_STAR: // use LDL2DFA algorithm as in de2021?
                compAutomaton = new Concatenation<>().transform(left, right);
                compAutomaton = new Reducer<>().transform(compAutomaton);
                compAutomaton = new Star<>().transform(compAutomaton);
                compAutomaton = new Reducer<>().transform(compAutomaton);
                break;
            default:
                throw new IllegalArgumentException("Not implemented yet: " + type);

//            LDLf_TEMP_NOT,
//            LDLf_TEMP_IMPL,
//            LDLf_TEMP_DOUBLEIMPL,
//            LDLf_LOCAL_IMPL,
//            LDLf_LOCAL_DOUBLEIMPL,
        }

//        compAutomaton = new Reducer<>().transform(compAutomaton);

        return compAutomaton;
    }

    private LDLfFormula regExpAtomicLocal2LDLf(RegExp regExp) {
        LDLfFormula ldlfFormula;

        if (!(regExp instanceof RegExpLocal)) {
            throw new IllegalArgumentException("Parse to LDL only works on RegExpLocal: " + regExp.getFormulaType());
        }

        FormulaType type = regExp.getFormulaType();
        switch (type) {
            case RE_LOCAL_TRUE -> ldlfFormula = new LDLfLocalTrueFormula();
            case RE_LOCAL_FALSE -> ldlfFormula = new LDLfLocalFalseFormula();
            default -> {
                PropositionalFormula propForm = ((RegExpLocal) regExp).regExpLocal2Propositional();
                ldlfFormula = parseLocalFormula(propForm.toString());
            }
        }
        return ldlfFormula;
    }

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

    private LDLfFormula getEndFormula() {
        // [true]ff
        RegExp regExp = new RegExpLocalTrue();
        LDLfFormula ldl = new LDLfffFormula();
        return new LDLfBoxFormula(regExp, ldl);
    }

    private Automaton getComplementNotEpsilonAutomaton(Automaton automaton) {
        Automaton temp = automaton.clone();

        Set<State> states = temp.states();
        for (State s : states) {
            if (s.isInitial()) {
                /* To avoid accepting epsilon */
                if (s.isTerminal()) {
                    s.setTerminal(false);
                }
            } else {
                s.setTerminal(!s.isTerminal());
            }
        }

        return temp.clone();
    }

    private Automaton getComplementAutomaton(Automaton automaton) {
        Automaton temp = automaton.clone();

        Set<State> states = temp.states();
        for (State s : states) {
            s.setTerminal(!s.isTerminal());
        }

        return temp.clone();
    }

    private Automaton getEpsilonAcceptAutomaton(Automaton automaton) {
        Automaton temp = automaton.clone();

        Set<State> initials = temp.initials();
        for (State s : initials) {
            s.setTerminal(true);
        }

        return temp.clone();
    }
}
