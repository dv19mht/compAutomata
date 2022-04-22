package utils;

import compositionalUtils.MyConcatenation;
import formula.*;
import formula.ldlf.*;
import formula.regExp.RegExp;
import formula.regExp.RegExpLocal;
import formula.regExp.RegExpLocalTrue;
import formula.regExp.RegExpStar;
import net.sf.tweety.logics.pl.semantics.PossibleWorld;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import rationals.Automaton;
import rationals.NoSuchStateException;
import rationals.State;
import rationals.Transition;
import rationals.transformations.*;

import java.util.HashSet;
import java.util.Set;

import static utils.ParserUtils.parseLocalFormula;

public class CompAutomatonUtils {

    public static Automaton LDLfToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps) {
        Automaton automaton;

        /*
         * Base case when the formula is an atomic proposition
         */
        if (formula instanceof AtomicFormula) {
            automaton = getElementaryAutomaton(formula, ps);
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

    private static Automaton regexpToAutomaton(boolean declare, RegExp regExp, PropositionalSignature ps) {
        Automaton automaton;

        /* Base case when expression is atomic proposition or local formula */
        if (regExp instanceof AtomicFormula || regExp instanceof LocalFormula) { //RE_LOCAL_VAR, RE_LOCAL_TRUE, RE_LOCAL__FALSE
            LDLfFormula ldlfFormula = regExpAtomicLocal2LDLf(regExp);
            automaton = LDLfToAutomaton(declare, ldlfFormula, ps);
            automaton = compositionAutomatonFactory(ldlfFormula.getFormulaType(), automaton, null);
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

    private static Automaton compositionAutomatonFactory(FormulaType type, Automaton left, Automaton right) {
        Automaton compAutomaton;

        switch (type) {
            case LDLf_LOCAL_TRUE:
            case LDLf_LOCAL_FALSE:
            case LDLf_LOCAL_VAR:
            case LDLf_tt:
            case LDLf_ff:
                compAutomaton = left;
                break;
            case LDLf_LOCAL_NOT:
                /*
                To avoid accepting epsilon after complement
                 */
                compAutomaton = getComplementNotEpsilonAutomaton(left);
                break;
            case LDLf_LOCAL_AND:
            case LDLf_TEMP_AND:
                compAutomaton = new Mix<>().transform(left, right);
                break;
            case LDLf_LOCAL_OR:
            case LDLf_TEMP_OR:
                compAutomaton = new Union<>().transform(left, right);
                break;
            case LDLf_BOX:
                Automaton compRight = new Complement<>().transform(right);
                compAutomaton = new MyConcatenation<>().transform(left, compRight);
                compAutomaton = new Complement<>().transform(compAutomaton);
                break;
            case RE_CONCAT: // More needed?
            case LDLf_DIAMOND:
                compAutomaton = new MyConcatenation<>().transform(left, right);
                break;
//            case RE_TEST:
//                compAutomaton = left;
//                break;
            case RE_STAR: // use LDL2DFA algorithm as in de2021?
                compAutomaton = new Concatenation<>().transform(left, right);
                compAutomaton = new Star<>().transform(compAutomaton);
                break;
            default:
                throw new IllegalArgumentException("Not implemented yet: " + type);

//            LDLf_TEMP_NOT,
//            LDLf_TEMP_IMPL,
//            LDLf_TEMP_DOUBLEIMPL,
//            LDLf_LOCAL_IMPL,
//            LDLf_LOCAL_DOUBLEIMPL,
        }

        return compAutomaton;
    }

    private static Automaton getElementaryAutomaton(LDLfFormula formula, PropositionalSignature ps) {
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
//            if (!automaton.accessibleStates().contains(endState)) {
//                endState.setTerminal(false);
//            }

//            addLoopingTransitions(labels, falseState, falseState, automaton);
        }

        automaton = new Reducer<>().transform(automaton);

        return automaton;
    }

    private static void addLoopingTransitions(Set<PossibleWorld> labels, State from, State to, Automaton automaton) {
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

    private static LDLfFormula regExpAtomicLocal2LDLf(RegExp regExp) {
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

    // [true]ff
    private static LDLfFormula getEndFormula() {
        RegExp regExp = new RegExpLocalTrue();
        LDLfFormula ldl = new LDLfffFormula();
        return new LDLfBoxFormula(regExp, ldl);
    }

    private static Automaton getComplementNotEpsilonAutomaton(Automaton automaton) {
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

}
