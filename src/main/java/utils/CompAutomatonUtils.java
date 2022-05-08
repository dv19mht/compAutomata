package utils;

import automaton.EmptyTrace;
import automaton.PossibleWorldWrap;
import automaton.QuotedFormulaStateFactory;
import automaton.QuotedFormulaStateFactory.QuotedFormulaState;
import automaton.TransitionLabel;
import formula.*;
import formula.ldlf.*;
import formula.ltlf.LTLfFormula;
import formula.quotedFormula.QuotedFormula;
import formula.quotedFormula.QuotedVar;
import formula.regExp.*;
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

public class CompAutomatonUtils {

    public static Automaton LDLfToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps) {
        return LDLfToAutomaton(declare, formula, ps, System.currentTimeMillis(), Long.MAX_VALUE);
    }

    public static Automaton LDLfToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;

        /*
         * Base case when the formula is an atomic proposition, i.e. 'tt' or 'ff'
         */
        if (formula instanceof AtomicFormula) {
            automaton = getElementaryAutomaton(formula, ps);
            return automaton;
        } else if ((System.currentTimeMillis() - timeStarted) > timeLimit) {
            // time limit reached
            return new Automaton();
        }

        /* Else parse subformula */
        if (formula instanceof UnaryFormula) {
            automaton = unaryToAutomaton(declare, formula, ps, timeStarted, timeLimit);
        } else if (formula instanceof BinaryFormula) {
            automaton = binaryToAutomaton(declare, formula, ps, timeStarted, timeLimit);
        } else if (formula instanceof TemporalFormula) {
            // Diamond or Box formula
            if (formula instanceof LDLfDiamondFormula) {
                automaton = diamondToAutomaton(declare, formula, ps, timeStarted, timeLimit);
            } else if (formula instanceof LDLfBoxFormula) {
                automaton = boxToAutomaton(declare, formula, ps, timeStarted, timeLimit);
            } else {
                throw new IllegalArgumentException("Unknown temporal formula " + formula);
            }
        } else {
            throw new IllegalArgumentException("Illegal formula " + formula);
        }

        automaton = new Reducer<>().transform(automaton);

        return automaton;
    }

    private static Automaton boxToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        Automaton rhoLeftAutomaton;
        Automaton rhoRightAutomaton;
        Automaton phiAutomaton;

        LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) formula;
        RegExp rho = tFormula.getRegExp();
        LDLfFormula phi = tFormula.getGoalFormula();

        /* [psi?]phi = !psi || phi */
        if (rho instanceof RegExpTest) {
            rhoLeftAutomaton = regexpToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);

            Automaton rhoComplement = new SinkComplete().transform(rhoLeftAutomaton);
            rhoComplement = new Complement<>().transform(rhoComplement);
            automaton = new Union<>().transform(rhoComplement, phiAutomaton);
        }

        /* [rho1 ; rho2]phi = [rho1][rho2]phi */
        else if (rho instanceof RegExpConcat) {
            RegExp leftFormula = ((RegExpConcat) rho).getLeftFormula();
            RegExp rightFormula = ((RegExpConcat) rho).getRightFormula();

            rhoLeftAutomaton = regexpToAutomaton(declare, leftFormula, ps, timeStarted, timeLimit);
            rhoRightAutomaton = regexpToAutomaton(declare, rightFormula, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);

            /* [rho2]phi = !<rho2>!phi */
            automaton = complementDiamondFormula(rhoRightAutomaton, phiAutomaton);

            if (leftFormula instanceof RegExpTest) {
                /* [psi ; rho2]phi = !psi || [rho2]phi */
                Automaton rhoLeftComplement = new SinkComplete().transform(rhoLeftAutomaton);
                rhoLeftComplement = new Complement<>().transform(rhoLeftComplement);
                automaton = new Union<>().transform(rhoLeftComplement, automaton);
            } else {
                /* [rho1 ; rho2]phi = [rho1][rho2]phi (phi = [rho2]phi at this point) */
                automaton = complementDiamondFormula(rhoLeftAutomaton, automaton);
            }

            if (rightFormula instanceof RegExpTest) {
                throw new IllegalArgumentException("Right regexp should not be a test formula: " + rightFormula);
            }

        }

        /* If rho* with tests, use ldlf2nfa algorithm */
        else if (rho instanceof RegExpStar && checkRegExpHasTest(rho)) {
                /*
                Use top-down algorithm if star and has tests
                 */
                System.err.println("Using LDLF2DFA on " + formula);
//                  timeLimit = System.currentTimeMillis() - timeStarted;
                automaton = AutomatonUtils.ldlf2Automaton(declare, formula, ps, timeLimit);
//                  automaton = CompAutomatonUtils.ldlf2AutomatonComp(declare, formula, ps, timeLimit);
                automaton = new Reducer<>().transform(automaton);
        }

        /* [rho]phi = !<rho>!phi */
        else {
            /*
            Proceed with compositional algorithm
             */
//                System.err.println("Using COMPOSITIONAL on " + formula);
            rhoLeftAutomaton = regexpToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = complementDiamondFormula(rhoLeftAutomaton, phiAutomaton);
        }

        return automaton;
    }

    private static Automaton complementDiamondFormula(Automaton rho, Automaton phi) {
        Automaton automaton;

        Automaton phiComplement = new SinkComplete().transform(phi);
        phiComplement = new Complement<>().transform(phiComplement);
        automaton = new Concatenation<>().transform(rho, phiComplement);
        automaton = new Reducer<>().transform(automaton);
        automaton = new SinkComplete().transform(automaton);
        automaton = new Complement<>().transform(automaton);

        return automaton;
    }

    private static Automaton diamondToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        Automaton rhoLeftAutomaton;
        Automaton rhoRightAutomaton;
        Automaton phiAutomaton;

        LDLfTempOpTempFormula tFormula = (LDLfTempOpTempFormula) formula;
        RegExp rho = tFormula.getRegExp();
        LDLfFormula phi = tFormula.getGoalFormula();

        /* <psi?>phi = psi && phi */
        if (rho instanceof RegExpTest) {
            rhoLeftAutomaton = regexpToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = new Mix<>().transform(rhoLeftAutomaton, phiAutomaton);
        }

        /* <rho1 ; rho2>phi = <rho1><rho2>phi */
        else if (rho instanceof RegExpConcat) {
            RegExp leftFormula = ((RegExpConcat) rho).getLeftFormula();
            RegExp rightFormula = ((RegExpConcat) rho).getRightFormula();

            rhoLeftAutomaton = regexpToAutomaton(declare, leftFormula, ps, timeStarted, timeLimit);
            rhoRightAutomaton = regexpToAutomaton(declare, rightFormula, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);

            automaton = new Concatenation<>().transform(rhoRightAutomaton, phiAutomaton);

            if (leftFormula instanceof RegExpTest) {
                automaton = new Mix<>().transform(rhoLeftAutomaton, automaton);
            } else {
                automaton = new Concatenation<>().transform(rhoLeftAutomaton, automaton);
            }

            if (rightFormula instanceof RegExpTest) {
                throw new IllegalArgumentException("Right regexp should not be a test formula: " + rightFormula);
            }

        }

        /*
        If rho* with tests, use ldlf2nfa algorithm
         */
        else if (rho instanceof RegExpStar && checkRegExpHasTest(rho)) {
            /*
            Use top-down algorithm if star and has tests
             */
            System.err.println("Using LDLF2DFA on " + formula);
//                  timeLimit = System.currentTimeMillis() - timeStarted;
            automaton = AutomatonUtils.ldlf2Automaton(declare, formula, ps, timeLimit);
//                  automaton = CompAutomatonUtils.ldlf2AutomatonComp(declare, formula, ps, timeLimit);
        }

        else {
            /*
            Proceed with compositional algorithm
             */
//                System.err.println("Using COMPOSITIONAL on " + formula);
            rhoLeftAutomaton = regexpToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = new Concatenation<>().transform(rhoLeftAutomaton, phiAutomaton);
//            automaton = compositionAutomatonFactory(formula.getFormulaType(), rho, rhoLeftAutomaton, phiAutomaton);
        }

        return automaton;
    }

    private static Automaton binaryToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        BinaryFormula bFormula = (BinaryFormula) formula;
        LDLfFormula left = (LDLfFormula) bFormula.getLeftFormula();
        LDLfFormula right = (LDLfFormula) bFormula.getRightFormula();
        Automaton leftAutomaton = LDLfToAutomaton(declare, left, ps, timeStarted, timeLimit);
        Automaton rightAutomaton = LDLfToAutomaton(declare, right, ps, timeStarted, timeLimit);

        if (formula instanceof LDLfTempAndFormula) {
            automaton = new Mix<>().transform(leftAutomaton, rightAutomaton);
        } else if (formula instanceof LDLfTempOrFormula) {
            automaton = new Union<>().transform(leftAutomaton, rightAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal binary formula " + formula);
        }
//        automaton = compositionAutomatonFactory(formula.getFormulaType(), null, leftAutomaton, rightAutomaton);
        return automaton;
    }

    private static Automaton unaryToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        UnaryFormula uFormula = (UnaryFormula) formula;
        LDLfFormula nested = (LDLfFormula) uFormula.getNestedFormula();
        automaton = LDLfToAutomaton(declare, nested, ps, timeStarted, timeLimit);
//        automaton = compositionAutomatonFactory(formula.getFormulaType(), null, automaton, null);
        return automaton;
    }

    public static LDLfFormula stringToNnfLDLf(String input) {
        LTLfFormula ltl = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        return ldl;
    }

    private static Automaton regexpToAutomaton(boolean declare, RegExp regExp, PropositionalSignature ps) {
        return regexpToAutomaton(declare, regExp, ps, System.currentTimeMillis(), Long.MAX_VALUE);
    }

//    private static Automaton regexpToAutomaton(boolean declare, RegExp regExp, PropositionalSignature ps, long timeStarted, long timeLimit) {
//        Automaton automaton;
//
//        /* Base case when expression is atomic proposition or local formula */
//        if (regExp instanceof AtomicFormula || regExp instanceof LocalFormula) {
//            //RE_LOCAL_VAR, RE_LOCAL_TRUE, RE_LOCAL__FALSE
//            automaton = getElementaryAutomaton(regExp, ps);
//            return automaton;
//        } else if ((System.currentTimeMillis() - timeStarted) > timeLimit) {
//            // time limit reached
//            return new Automaton();
//        }
//
//        /* Else parse subformula */
//        if (regExp instanceof UnaryFormula) {
//            UnaryFormula uFormula = (UnaryFormula) regExp;
//            Formula nested = uFormula.getNestedFormula();
//
//            if (nested instanceof RegExp) {
//                automaton = regexpToAutomaton(declare, (RegExp) nested, ps, timeStarted, timeLimit);
//            } else if (nested instanceof LDLfFormula) {
//                //Special case when RegExpTest
//                automaton = LDLfToAutomaton(declare, (LDLfFormula) nested, ps, timeStarted, timeLimit);
//                return automaton; // do not send to compositionAutomatonFactory
//            } else {
//                throw new IllegalArgumentException("Nested formula of unknown type " + nested.getClass());
//            }
//
//            /* rho* = (<rho>end)* */
//            if (regExp instanceof RegExpStar) {
//                Automaton end = LDLfToAutomaton(declare, FormulaUtils.generateLDLfEndedFormula(), ps, timeStarted, timeLimit);
//                automaton = new Concatenation<>().transform(automaton, end);
//                automaton = new Star<>().transform(automaton);
////                automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, automaton, end);
//            }
//
//            else {
//                throw new IllegalArgumentException("Unknown regexp unary " + regExp);
////                automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, automaton, null);
//            }
//        } else if (regExp instanceof BinaryFormula) {
//            BinaryFormula bFormula = (BinaryFormula) regExp;
//            RegExp left = (RegExp) bFormula.getLeftFormula();
//            RegExp right = (RegExp) bFormula.getRightFormula();
//            Automaton leftAutomaton = regexpToAutomaton(declare, left, ps, timeStarted, timeLimit);
//            Automaton rightAutomaton = regexpToAutomaton(declare, right, ps, timeStarted, timeLimit);
//            automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, leftAutomaton, rightAutomaton);
//        } else {
//            throw new IllegalArgumentException("Illegal regexp " + regExp);
//        }
//
//        return automaton;
//    }

    private static Automaton regexpToAutomaton(boolean declare, RegExp regExp, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;

        /* Base case when expression is atomic proposition or local formula */
        if (regExp instanceof AtomicFormula || regExp instanceof LocalFormula) {
            //RE_LOCAL_VAR, RE_LOCAL_TRUE, RE_LOCAL__FALSE
            automaton = getElementaryAutomaton(regExp, ps);
            return automaton;
        } else if ((System.currentTimeMillis() - timeStarted) > timeLimit) {
            // time limit reached
            return new Automaton();
        }

        /* Else parse subformula */
        else if (regExp instanceof UnaryFormula) {
            UnaryFormula uFormula = (UnaryFormula) regExp;
            Formula nested = uFormula.getNestedFormula();

            if (nested instanceof RegExp) {
                automaton = regexpToAutomaton(declare, (RegExp) nested, ps, timeStarted, timeLimit);
            } else if (nested instanceof LDLfFormula) {
                //Special case when RegExpTest
                automaton = LDLfToAutomaton(declare, (LDLfFormula) nested, ps, timeStarted, timeLimit);
                return automaton; // do not send to compositionAutomatonFactory
            } else {
                throw new IllegalArgumentException("Nested formula of unknown type " + nested.getClass());
            }

            if (regExp instanceof RegExpStar) {
                /* rho* = (<rho>end)* */
                Automaton end = LDLfToAutomaton(declare, FormulaUtils.generateLDLfEndedFormula(), ps, timeStarted, timeLimit);
                automaton = new Concatenation<>().transform(automaton, end);
                automaton = new Star<>().transform(automaton);
//                automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, automaton, end);
            }
        } else if (regExp instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) regExp;
            RegExp left = (RegExp) bFormula.getLeftFormula();
            RegExp right = (RegExp) bFormula.getRightFormula();
            Automaton leftAutomaton = regexpToAutomaton(declare, left, ps, timeStarted, timeLimit);
            Automaton rightAutomaton = regexpToAutomaton(declare, right, ps, timeStarted, timeLimit);

            if (regExp instanceof RegExpConcat) {
                automaton = new Concatenation<>().transform(leftAutomaton, rightAutomaton);
            } else {
                throw new IllegalArgumentException("Unknown regexp binary " + regExp);
            }
//            automaton = compositionAutomatonFactory(regExp.getFormulaType(), null, leftAutomaton, rightAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal regexp " + regExp);
        }

        automaton = new Reducer<>().transform(automaton);
        return automaton;
    }

    public static boolean hasTests(Formula formula) {
        if (formula instanceof LDLfTempOpTempFormula) {
            LDLfTempOpTempFormula tempLdlf = (LDLfTempOpTempFormula) formula;
            return (checkRegExpHasTest(tempLdlf.getRegExp()));
        } else {
            return false;
        }
    }

    public static boolean checkRegExpHasTest(RegExp regExp) {
        boolean hasTest;

        /* Base case when expression is a test formula or atomic / local */
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
                hasTest = checkRegExpHasTest((RegExp) nested);
            } else {
                throw new IllegalArgumentException("Nested formula of unknown type " + nested.getClass());
            }
        } else if (regExp instanceof BinaryFormula) {
            BinaryFormula bFormula = (BinaryFormula) regExp;
            RegExp left = (RegExp) bFormula.getLeftFormula();
            RegExp right = (RegExp) bFormula.getRightFormula();
            hasTest = checkRegExpHasTest(left);
            if (!hasTest) {
                hasTest = checkRegExpHasTest(right);
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
                    compAutomaton = left; //.clone();
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
                    compAutomaton = left; // .clone();
                } else {
                    compAutomaton = new Concatenation<>().transform(left, right);
                    /*
                    To prevent reduction to empty automaton
                     */
                    if (new isEmpty<>().test(compAutomaton)) {
                        compAutomaton = right; //.clone();
                    }
                }
                break;

            case RE_STAR:
                if (new isEmpty<>().test(left)) {
                    compAutomaton = left; //.clone();
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

        Set<PossibleWorld> labels = buildAllLables(ps);

        if (formula instanceof LDLfttFormula) {
            initialState = automaton.addState(true, true);
            addLoopingTransitions(labels, initialState, initialState, automaton);
        } else if (formula instanceof LDLfffFormula) {
            initialState = automaton.addState(true, false);
            addLoopingTransitions(labels, initialState, initialState, automaton);
        }  else {
            if (!(formula instanceof RegExpLocal)) {
                throw new IllegalArgumentException("Formula is not a RegExpLocal: " + formula.getFormulaType());
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

    private static Set<PossibleWorld> buildAllLables(PropositionalSignature ps) {
        Set<PossibleWorld> labels = new HashSet<>();

        for (Proposition p : ps) {
            Set<Proposition> propSet = new HashSet<>();
            propSet.add(p);

            /* Use Wrap to use the same labels as ldlf2nfa-algorithm */
            labels.add(new PossibleWorldWrap(propSet));
        }
        return labels;
    }

    private static void addLoopingTransitions(Set<PossibleWorld> labels, State from, State to, Automaton automaton) {
        for (PossibleWorld label : labels) {
            Transition<PossibleWorld> transition = new Transition<>(from, label, to);

            try {
                automaton.addTransition(transition);
            } catch (NoSuchStateException e) {
                e.printStackTrace();
            }
        }
    }

    private static void handleIfFinal(Automaton automaton, QuotedFormulaState destinationState, Set<PossibleWorld> allLabels) {
        /*
        If state is the sink final state (true state), i.e., the state with the empty set of quoted formulas,
        then set as final and add all looping transitions.
         */
        if (destinationState.getFormulaSet().isEmpty()) {
            destinationState.setTerminal(true);
            addLoopingTransitions(allLabels, destinationState, destinationState, automaton);
            return;
        }

        /*
        Create the emptyTrace special label!
         */
        TransitionLabel emptyTrace = new EmptyTrace();
        QuotedFormula currentFormula = destinationState.getQuotedConjunction();
        QuotedFormula deltaResult = currentFormula.delta(emptyTrace);
        Set<Set<QuotedVar>> allMinimalModels = deltaResult.getMinimalModels();

        /*
        If the set of possible models is empty, then it is the false state. So return
         */
        if (allMinimalModels.isEmpty()) {
            return;
        }

        /*
        Otherwise, it has some model. Check if there is the empty one (i.e., true) among those.
        If this is the case, then set it as final.
         */
        for (Set<QuotedVar> model : allMinimalModels) {
            if (model.isEmpty()) {
                destinationState.setTerminal(true);
                return;
            }
        }
    }

    private static QuotedFormulaState getStateIfExists(Automaton a, Set<QuotedVar> sqv) {
        QuotedFormulaState result = null;
        Set<QuotedFormulaState> states = a.states();
        for (QuotedFormulaState s : states) {
            if (s.getFormulaSet() != null && s.getFormulaSet().equals(sqv)) {
                return s;
            }
        }

        return result;
    }

    public static Automaton ldlf2AutomatonComp(boolean declare, LDLfFormula initialFormula, PropositionalSignature ps, long timeLimit) {
        long timeStarted = System.currentTimeMillis();

        // Automaton initialization: empty automaton
        QuotedFormulaStateFactory stateFactory = new QuotedFormulaStateFactory();
        Automaton automaton = new Automaton(stateFactory);
        stateFactory.setAutomaton(automaton);

        /*
        Algorithm data structures
         */
        LinkedList<QuotedFormulaState> toAnalyze = new LinkedList<>();

        /*
        Get all possible models for the signature and depending on the declare assumption.
         */
        Set<PossibleWorld> allLabels = buildAllLables(ps); // changed from <TransitionLabel>

        /*
        Initialize the data structure for the "false" state.
         */
        QuotedFormulaState falseState = (QuotedFormulaState) stateFactory.create(false, false, null);

        // Initialize the data structure for the initial state;
        Set<QuotedVar> initialStateFormulas = new HashSet<>();
        initialStateFormulas.add(new QuotedVar(initialFormula));

        /*
        Creation of the initial state.
         */
        QuotedFormulaState initialState = (QuotedFormulaState) stateFactory.create(true, false, initialStateFormulas);

        // Check if final and perform operations accordingly
        handleIfFinal(automaton, initialState, allLabels);

        // Add the initial state to the set of state to be analyzed
        toAnalyze.add(initialState);

        /*
        All transition loops in the false state
         */
        addLoopingTransitions(allLabels, falseState, falseState, automaton);

        // Cycle on states yet to be analyzed
        while (!toAnalyze.isEmpty() && ((System.currentTimeMillis() - timeStarted) < timeLimit)) {
            QuotedFormulaState currentState = toAnalyze.getFirst();
            // Conjunction of the QuotedVar belonging to the current state
            QuotedFormula currentFormula = currentState.getQuotedConjunction();

            // For each possible label, call the delta function on currentFormula
            for (PossibleWorld label : allLabels) {
                // Hack, all labels are PossibleWorldWraps which implement TransitionLabel
                QuotedFormula deltaResult = currentFormula.delta((TransitionLabel) label);

                // Compute the minimal interpretations satisfying deltaResult, that is, all the q'
                Set<Set<QuotedVar>> newStateSetFormulas = deltaResult.getMinimalModels();

                // newStateFormulas empty means that the current interpretation lead to the "false" state.
                if (newStateSetFormulas.isEmpty()) {
                    // Add the transition (currentState, world, falseState)
                    Transition<PossibleWorld> t = new Transition<>(currentState, label, falseState);
                    try {
                        automaton.addTransition(t);
                    } catch (NoSuchStateException e) {
                        e.printStackTrace();
                    }
                }

                // Otherwise, the transition DOES NOT lead to the false state.
                else {
                    for (Set<QuotedVar> newStateFormulas : newStateSetFormulas) {
                        //Add the new state if new, or give me the already existing one with the same Set<QuotedVar>
                        QuotedFormulaState destinationState = getStateIfExists(automaton, newStateFormulas);

                        if (destinationState == null) {
                            // conjunct QuotedVar
                            // if tests, stop
                            LDLfFormula conjunctFormula = null;
                            boolean hasTests = false;

                            Iterator<QuotedVar> i1 = newStateFormulas.iterator();
                            while (i1.hasNext()) {
                                LDLfFormula varForm = i1.next().getUnquotedFormula();
                                if (hasTests(varForm)) {
                                    hasTests = true;
                                    break;
                                }

                                if (conjunctFormula == null) {
                                    conjunctFormula = varForm;
                                } else {
                                    conjunctFormula = new LDLfTempAndFormula(conjunctFormula, varForm);
                                }
                            }

                            /* if still null it is the true state */
                            if (!hasTests && conjunctFormula != null) {
                                System.err.println("Creating C-LDLf automaton from " + conjunctFormula);
                                destinationState = (QuotedFormulaState) stateFactory.create(false, false, newStateFormulas);
                                Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, conjunctFormula, ps, timeStarted, timeLimit);
                                connectAutomatons(automaton, comp, destinationState);
                            } else {
                                //else
                                destinationState = (QuotedFormulaState) stateFactory.create(false, false, newStateFormulas);
                                handleIfFinal(automaton, destinationState, allLabels);

                                // Add to the set of states to be analyzed only if it is not the true state!
                                if (!destinationState.getFormulaSet().isEmpty()) {
                                    toAnalyze.addLast(destinationState);
                                }
                            }
                        }

                        // Add the transition (currentState, world, destinationState)
                        Transition<PossibleWorld> t = new Transition<>(currentState, label, destinationState);
                        try {
                            automaton.addTransition(t);
                        } catch (NoSuchStateException e) {
                            e.printStackTrace();
                        }
                    }

                }

                /* timeout */
                if ((System.currentTimeMillis() - timeStarted) > timeLimit) {
                    break;
                }
            }
            toAnalyze.remove(currentState);
        }
        return automaton;
    }

    private static void connectAutomatons(Automaton mainAutomaton, Automaton comp, QuotedFormulaState destinationState) {
        QuotedFormulaStateFactory stateFactory = (QuotedFormulaStateFactory) mainAutomaton.getStateFactory();
        HashMap<State, State> map = new HashMap<>();
        Iterator<State> i2 = comp.states().iterator();
        while (i2.hasNext()) {
            State e = i2.next();
            State n = stateFactory.create(false, e.isTerminal(), new HashSet<>()); // could produce several "equal" states
            map.put(e, n);

            if (e.isInitial()) {
                // Connect automatons (destinationState, epsilon, initial)
                Transition<PossibleWorld> t2 = new Transition<>(destinationState, null, map.get(e));
                try {
                    mainAutomaton.addTransition(t2);
                } catch (NoSuchStateException err) {
                    err.printStackTrace();
                }
            }
        }

        Iterator<Transition<PossibleWorld>> i3 = comp.delta().iterator();
        while (i3.hasNext()) {
            Transition<PossibleWorld> te = i3.next();
            Transition<PossibleWorld> tn = new Transition<>(map.get(te.start()), te.label(), map.get(te.end()));

            try {
                mainAutomaton.addTransition(tn);
            } catch (NoSuchStateException e) {
                e.printStackTrace();
            }
        }
    }

}
