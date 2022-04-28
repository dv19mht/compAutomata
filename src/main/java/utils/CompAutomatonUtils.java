package utils;

import compositionalUtils.MyConcatenation;
import formula.*;
import formula.ldlf.*;
import formula.ltlf.LTLfFormula;
import formula.regExp.RegExp;
import formula.regExp.RegExpLocal;
import formula.regExp.RegExpStar;
import formula.regExp.RegExpTest;
import net.sf.tweety.logics.pl.semantics.PossibleWorld;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import rationals.Automaton;
import rationals.NoSuchStateException;
import rationals.State;
import rationals.Transition;
import rationals.properties.isEmpty;
import rationals.transformations.*;

import java.util.*;

import static utils.ParserUtils.parseLTLfFormula;

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
            automaton = compositionAutomatonFactory(formula.getFormulaType(), null, automaton, null);
        } else if (formula instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) formula;
            LDLfFormula left = (LDLfFormula) bFormula.getLeftFormula();
            LDLfFormula right = (LDLfFormula) bFormula.getRightFormula();
            Automaton leftAutomaton = LDLfToAutomaton(declare, left, ps);
            Automaton rightAutomaton = LDLfToAutomaton(declare, right, ps);
            automaton = compositionAutomatonFactory(formula.getFormulaType(), null, leftAutomaton, rightAutomaton);
        } else if (formula instanceof TemporalFormula) {
//            System.err.println("Formula: " + formula);
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) formula;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();

            if (regexpHasTest(reg)) {
                /*
                Use top-down algorithm
                 */
//                System.err.println("Using LDLF2DFA");
                automaton = AutomatonUtils.ldlf2Automaton(declare, formula, ps);
                automaton = new Reducer<>().transform(automaton);
                automaton = CompAutomatonUtils.convertLDLf2DFAtoCompositional(automaton);
            } else {
                /*
                Proceed with compositional algorithm
                 */
//                System.err.println("Using COMPOSITIONAL");
                Automaton regAutomaton = regexpToAutomaton(declare, reg, ps);
                Automaton goalAutomaton = LDLfToAutomaton(declare, goal, ps);
                automaton = compositionAutomatonFactory(formula.getFormulaType(), reg, regAutomaton, goalAutomaton);
            }
        } else {
            throw new IllegalArgumentException("Illegal formula " + formula);
        }

        return automaton;
    }

    public static LDLfFormula stringToNnfLDLf(String input) {
        LTLfFormula ltl = parseLTLfFormula(input);
        LDLfFormula ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        return ldl;
    }

    private static Automaton regexpToAutomaton(boolean declare, RegExp regExp, PropositionalSignature ps) {
        Automaton automaton;

        /* Base case when expression is atomic proposition or local formula */
        if (regExp instanceof AtomicFormula || regExp instanceof LocalFormula) {
            //RE_LOCAL_VAR, RE_LOCAL_TRUE, RE_LOCAL__FALSE
            automaton = getElementaryAutomaton(regExp, ps);
            return automaton;
        }

        /* Else parse subformula */
        if (regExp instanceof UnaryFormula) {
            UnaryFormula uFormula = (UnaryFormula) regExp;
            Formula nested = uFormula.getNestedFormula();
            if (nested instanceof RegExp) {
                automaton = regexpToAutomaton(declare, (RegExp) nested, ps);
            } else if (nested instanceof LDLfFormula) {
                //Special case when RegExpTest
                automaton = LDLfToAutomaton(declare, (LDLfFormula) nested, ps);
            } else {
                throw new IllegalArgumentException("Nested formula of unknown type " + nested.getClass());
            }

            if (regExp instanceof RegExpStar) {
                Automaton end = LDLfToAutomaton(declare, FormulaUtils.generateLDLfEndedFormula(), ps);
                automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, automaton, end);
            } else {
                automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, automaton, null);
            }
        } else if (regExp instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) regExp;
            RegExp left = (RegExp) bFormula.getLeftFormula(); //Can be LDLfFormula?
            RegExp right = (RegExp) bFormula.getRightFormula(); //Can be LDLfFormula?
            Automaton leftAutomaton = regexpToAutomaton(declare, left, ps);
            Automaton rightAutomaton = regexpToAutomaton(declare, right, ps);
            automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, leftAutomaton, rightAutomaton);
        } else if (regExp instanceof TemporalFormula) {
            LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) regExp;
            RegExp reg = tFormula.getRegExp();
            LDLfFormula goal = tFormula.getGoalFormula();
            Automaton regAutomaton = regexpToAutomaton(declare, reg, ps);
            Automaton goalAutomaton = LDLfToAutomaton(declare, goal, ps);
            automaton = compositionAutomatonFactory(regExp.getFormulaType(), reg, regAutomaton, goalAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal regexp " + regExp);
        }

        return automaton;
    }

    public static boolean regexpHasTest(RegExp regExp) {
        boolean hasTest;

        /* Base case when expression is a test formula or atomic/local */
        if (regExp instanceof RegExpTest) {
            return true;
        } else if (regExp instanceof AtomicFormula || regExp instanceof LocalFormula) {
            return false;
        }

        /* Else parse subformula */
        if (regExp instanceof UnaryFormula) {
            UnaryFormula uFormula = (UnaryFormula) regExp;
            Formula nested = uFormula.getNestedFormula();
            if (nested instanceof RegExp) {
                hasTest = regexpHasTest((RegExp) nested);
            } else {
                throw new IllegalArgumentException("Nested formula of unknown type " + nested.getClass());
            }
        } else if (regExp instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) regExp;
            RegExp left = (RegExp) bFormula.getLeftFormula(); //Can be LDLfFormula?
            RegExp right = (RegExp) bFormula.getRightFormula(); //Can be LDLfFormula?
            hasTest = regexpHasTest(left);
            if (!hasTest) {
                hasTest = regexpHasTest(right);
            }
        } else {
            throw new IllegalArgumentException("Illegal regexp " + regExp);
        }

        return hasTest;
    }

    public static Automaton compositionAutomatonFactory(FormulaType type, RegExp nested, Automaton left, Automaton right) {
        Automaton compAutomaton;

        switch (type) {
            case LDLf_TEMP_AND:
                compAutomaton = new Mix<>().transform(left, right);
                break;

            case LDLf_TEMP_OR:
                compAutomaton = new Union<>().transform(left, right);
                break;

            case LDLf_BOX:
                if (new isEmpty<>().test(left)) {
                    compAutomaton = left.clone();
                } else {
                    Automaton compRight = new Complement<>().transform(right);
                    compAutomaton = new Concatenation<>().transform(left, compRight);
                    compAutomaton = new Reducer<>().transform(compAutomaton);
                    compAutomaton = new SinkComplete().transform(compAutomaton);
                }
                compAutomaton = new Complement<>().transform(compAutomaton);
                break;

            case RE_CONCAT: // More needed?
            case LDLf_DIAMOND:
                if (new isEmpty<>().test(left)) {
                    compAutomaton = left.clone();
                } else {
                    compAutomaton = new Concatenation<>().transform(left, right);
                    /*
                    To prevent reduction to empty automaton
                     */
                    if (new isEmpty<>().test(compAutomaton)) {
                        compAutomaton = right.clone();
                    }
                }
                break;

            case RE_STAR:
                if (new isEmpty<>().test(left)) {
                    compAutomaton = left.clone();
                } else {
                    compAutomaton = new Concatenation<>().transform(left, right);
                }

                compAutomaton = new Star<>().transform(compAutomaton);
                break;

            default:
                throw new IllegalArgumentException("Not implemented yet: " + type);
        }

        compAutomaton = new Reducer<>().transform(compAutomaton);

        return compAutomaton;
    }

    public static Automaton getElementaryAutomaton(Formula formula, PropositionalSignature ps) {
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
        }  else {
            if (!(formula instanceof LocalFormula)) {
                throw new IllegalArgumentException("Formula is not a LocalFormula: " + formula.getFormulaType());
            }

            initialState = automaton.addState(true, false);
            endState = automaton.addState(false, true);
            falseState = automaton.addState(false, false);

            PropositionalFormula propFormula = ((RegExpLocal) formula).regExpLocal2Propositional();

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

    public static Automaton convertLDLf2DFAtoCompositional(Automaton ldlf2dfa) {
        Automaton compAutomaton = new Automaton();
        HashMap<State, State> map = new HashMap<>();

        /*
        Add all states
         */
        Iterator<State> i1 = ldlf2dfa.states().iterator();
        while (i1.hasNext()) {
            State e = i1.next();
            State n = compAutomaton.addState(e.isInitial(), e.isTerminal());
            map.put(e, n);
        }

        /*
        Add all transitions
         */
        Iterator<Transition<PossibleWorld>> i2 = ldlf2dfa.delta().iterator();
        while (i2.hasNext()) {
            Transition<PossibleWorld> t = i2.next();

            /*
            Convert labels from PossibleWorldWrap
             */
            Iterator<Proposition> i3 = t.label().iterator();
            PossibleWorld pw = new PossibleWorld();
            while (i3.hasNext()) {
                pw.add(i3.next());
            }

            try {
                compAutomaton.addTransition(new Transition<>(map.get(t.start()), pw, map.get(t.end())));
            } catch (NoSuchStateException e) {
                e.printStackTrace();
            }
        }

        return compAutomaton;
    }

}
