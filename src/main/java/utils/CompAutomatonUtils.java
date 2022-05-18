package utils;

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
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import rationals.Automaton;
import rationals.NoSuchStateException;
import rationals.State;
import rationals.Transition;
import rationals.transformations.*;

import java.util.*;

/**
 * @author Mathias Hedqvist 2022-06-03
 */
public class CompAutomatonUtils {

    public static Automaton LDLfToAutomaton(boolean declare, LDLfFormula formula, PropositionalSignature ps) {
        return LDLfToAutomaton(declare, formula, ps, System.currentTimeMillis(), Long.MAX_VALUE);
    }

    public static Automaton LDLfToAutomaton(boolean declare, Formula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;

        /*
         * Base case when the formula is an atomic proposition, i.e. 'tt', 'ff' or propositional regexp
         */
        if (formula instanceof AtomicFormula || formula instanceof LocalFormula) {
            automaton = getElementaryAutomaton(formula, declare, ps);
            return automaton;
        } else if ((System.currentTimeMillis() - timeStarted) > timeLimit) {
            // time out
            return new Automaton();
        }

        /* Else parse subformula */
        if (formula instanceof UnaryFormula) {
            automaton = unaryToAutomaton(declare, (UnaryFormula) formula, ps, timeStarted, timeLimit);
        } else if (formula instanceof BinaryFormula) {
            automaton = binaryToAutomaton(declare, (BinaryFormula) formula, ps, timeStarted, timeLimit);
        } else if (formula instanceof LDLfDiamondFormula) {
            if (checkForTestWithinStar(formula)) {
                // calc time left
                long timeLeft = timeLimit - (System.currentTimeMillis() - timeStarted);
                automaton = ldlf2nfaComp(declare, (LDLfFormula) formula, ps, timeLeft);
//                automaton = AutomatonUtils.ldlf2Automaton(declare, (LDLfFormula) formula, ps, timeLeft);
            } else {
                automaton = diamondToAutomaton(declare, (LDLfDiamondFormula) formula, ps, timeStarted, timeLimit);
            }
        } else if (formula instanceof LDLfBoxFormula) {
            if (checkForTestWithinStar(formula)) {
                // calc time left
                long timeLeft = timeLimit - (System.currentTimeMillis() - timeStarted);
                automaton = ldlf2nfaComp(declare, (LDLfFormula) formula, ps, timeLeft);
//                automaton = AutomatonUtils.ldlf2Automaton(declare, (LDLfFormula) formula, ps, timeLeft);
            } else {
                automaton = boxToAutomaton(declare, (LDLfBoxFormula) formula, ps, timeStarted, timeLimit);
            }
        } else {
            throw new IllegalArgumentException("Illegal formula " + formula);
        }

        /* if time left, reduce */
        if ((System.currentTimeMillis() - timeStarted) < timeLimit) {
            automaton = new SinkComplete().transform(automaton);
            automaton = new Reducer<>().transform(automaton);
        }

        return automaton;
    }

    public static LDLfFormula stringToNnfLDLf(String input) {
        LTLfFormula ltl = ParserUtils.parseLTLfFormula(input);
        LDLfFormula ldl = ltl.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        return ldl;
    }

    /*
     * Only tested on nnf-LDLfFormula
     */
    public static boolean checkForTestWithinStar(Formula formula) {
        return checkForTestWithinStar(formula, false);
    }

    private static Automaton boxToAutomaton(boolean declare, LDLfBoxFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        Automaton rhoLeftAutomaton;
        Automaton phiAutomaton;

        RegExp rho = formula.getRegExp();
        LDLfFormula phi = formula.getGoalFormula();

        /* [psi?]phi = !psi || phi */
        if (rho instanceof RegExpTest) {
            rhoLeftAutomaton = LDLfToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);

            Automaton rhoComplement = new Complement<>().transform(rhoLeftAutomaton);
            automaton = new Union<>().transform(rhoComplement, phiAutomaton);
        }
        /* [rho1 ; rho2]phi = [rho1][rho2]phi */
        else if (rho instanceof RegExpConcat) {
            RegExp leftFormula = ((RegExpConcat) rho).getLeftFormula();
            RegExp rightFormula = ((RegExpConcat) rho).getRightFormula();

            // create [rho2]phi first, then [rho1]phi'
            LDLfFormula rho2phi = new LDLfBoxFormula(rightFormula, phi); // need to clone formulae?
            LDLfFormula rho1phi = new LDLfBoxFormula(leftFormula, rho2phi); // need to clone formulae?
            automaton = LDLfToAutomaton(declare, rho1phi, ps, timeStarted, timeLimit);
        }
        /* [rho1 + rho2]phi = [rho1]phi && [rho2]phi */
        else if (rho instanceof RegExpAltern) {
            RegExp leftFormula = ((RegExpAltern) rho).getLeftFormula();
            RegExp rightFormula = ((RegExpAltern) rho).getRightFormula();

            LDLfFormula rho1phi = new LDLfBoxFormula(leftFormula, phi);
            LDLfFormula rho2phi = new LDLfBoxFormula(rightFormula, phi);

            Automaton rho1 = LDLfToAutomaton(declare, rho1phi, ps, timeStarted, timeLimit);
            Automaton rho2 = LDLfToAutomaton(declare, rho2phi, ps, timeStarted, timeLimit);
            automaton = new Mix<>().transform(rho1, rho2);
        }

        else if (rho instanceof RegExpStar) {
            Formula nestedFormula = ((RegExpStar) rho).getNestedFormula();
            LDLfFormula rhoEnd = new LDLfDiamondFormula((RegExp) nestedFormula, FormulaUtils.generateLDLfEndedFormula());

            Automaton endAutomaton = LDLfToAutomaton(declare, rhoEnd, ps, timeStarted, timeLimit);
            endAutomaton = new Star<>().transform(endAutomaton);
            endAutomaton = new Reducer<>().transform(endAutomaton);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = complementDiamondFormula(endAutomaton, phiAutomaton);
        }
        /* [rho]phi = !<rho>!phi */
        else {
            rhoLeftAutomaton = LDLfToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = complementDiamondFormula(rhoLeftAutomaton, phiAutomaton);
        }

        return automaton;
    }

    private static Automaton diamondToAutomaton(boolean declare, LDLfDiamondFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        Automaton rhoLeftAutomaton;
        Automaton phiAutomaton;

        RegExp rho = formula.getRegExp();
        LDLfFormula phi = formula.getGoalFormula();

        /* <psi?>phi = psi && phi */
        if (rho instanceof RegExpTest) {
            rhoLeftAutomaton = LDLfToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = new Mix<>().transform(rhoLeftAutomaton, phiAutomaton);
        }
        /* <rho1 ; rho2>phi = <rho1><rho2>phi */
        else if (rho instanceof RegExpConcat) {
            RegExp leftFormula = ((RegExpConcat) rho).getLeftFormula();
            RegExp rightFormula = ((RegExpConcat) rho).getRightFormula();

            // create <rho2>phi first, then <rho1>phi'
            LDLfFormula rho2phi = new LDLfDiamondFormula(rightFormula, phi); // need to clone formulae?
            LDLfFormula rho1phi = new LDLfDiamondFormula(leftFormula, rho2phi); // need to clone formulae?
            automaton = LDLfToAutomaton(declare, rho1phi, ps, timeStarted, timeLimit);
        }
        /* <rho1 + rho2>phi = <rho1>phi || <rho2>phi */
        else if (rho instanceof RegExpAltern) {
            RegExp leftFormula = ((RegExpAltern) rho).getLeftFormula();
            RegExp rightFormula = ((RegExpAltern) rho).getRightFormula();

            LDLfFormula rho1phi = new LDLfDiamondFormula(leftFormula, phi);
            LDLfFormula rho2phi = new LDLfDiamondFormula(rightFormula, phi);

            Automaton rho1 = LDLfToAutomaton(declare, rho1phi, ps, timeStarted, timeLimit);
            Automaton rho2 = LDLfToAutomaton(declare, rho2phi, ps, timeStarted, timeLimit);
            automaton = new Union<>().transform(rho1, rho2);
        }
        /* <rho*>phi = (<rho>end)*phi */
        else if (rho instanceof RegExpStar) {
            Formula nestedFormula = ((RegExpStar) rho).getNestedFormula();
            LDLfFormula rhoEnd = new LDLfDiamondFormula((RegExp) nestedFormula, FormulaUtils.generateLDLfEndedFormula());

            Automaton endAutomaton = LDLfToAutomaton(declare, rhoEnd, ps, timeStarted, timeLimit);
            endAutomaton = new Star<>().transform(endAutomaton);
            endAutomaton = new Reducer<>().transform(endAutomaton);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = new Concatenation<>().transform(endAutomaton, phiAutomaton);
        }
        /* <rho>phi */
        else {
            rhoLeftAutomaton = LDLfToAutomaton(declare, rho, ps, timeStarted, timeLimit);
            phiAutomaton = LDLfToAutomaton(declare, phi, ps, timeStarted, timeLimit);
            automaton = new Concatenation<>().transform(rhoLeftAutomaton, phiAutomaton);
        }

        return automaton;
    }

    private static Automaton complementDiamondFormula(Automaton rho, Automaton phi) {
        Automaton automaton;

        Automaton phiComplement = new Complement<>().transform(phi);
        automaton = new Concatenation<>().transform(rho, phiComplement);
        automaton = new Reducer<>().transform(automaton);
        automaton = new SinkComplete().transform(automaton);
        automaton = new Complement<>().transform(automaton);

        return automaton;
    }

    private static Automaton binaryToAutomaton(boolean declare, BinaryFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        Automaton leftAutomaton = LDLfToAutomaton(declare, formula.getLeftFormula(), ps, timeStarted, timeLimit);
        Automaton rightAutomaton = LDLfToAutomaton(declare, formula.getRightFormula(), ps, timeStarted, timeLimit);

        if (formula instanceof LDLfTempAndFormula) {
            automaton = new Mix<>().transform(leftAutomaton, rightAutomaton);
        } else if (formula instanceof LDLfTempOrFormula) {
            automaton = new Union<>().transform(leftAutomaton, rightAutomaton);
        } else {
            throw new IllegalArgumentException("Illegal binary formula " + formula);
        }

        return automaton;
    }

    private static Automaton unaryToAutomaton(boolean declare, UnaryFormula formula, PropositionalSignature ps, long timeStarted, long timeLimit) {
        Automaton automaton;
        automaton = LDLfToAutomaton(declare, formula.getNestedFormula(), ps, timeStarted, timeLimit);
        return automaton;
    }

    private static boolean checkForTestWithinStar(Formula formula, boolean hasStar) {
        boolean hasTest;
        Formula nestedLeft;
        Formula nestedRight;

        /* base case when atomic, local or test and hasStar */
        if (formula instanceof AtomicFormula || formula instanceof LocalFormula) {
            return false;
        } else if (formula instanceof RegExpTest && hasStar) {
            return true;
        }

        if (formula instanceof UnaryFormula) {
            nestedLeft = ((UnaryFormula) formula).getNestedFormula();

            if (formula instanceof RegExpStar) {
                hasTest = checkForTestWithinStar(nestedLeft, true);
            } else {
                hasTest = checkForTestWithinStar(nestedLeft, hasStar);
            }
        } else if (formula instanceof BinaryFormula) {
            nestedLeft = ((BinaryFormula) formula).getLeftFormula();
            nestedRight = ((BinaryFormula) formula).getRightFormula();

            hasTest = checkForTestWithinStar(nestedLeft, hasStar);
            if (!hasTest) {
                hasTest = checkForTestWithinStar(nestedRight, hasStar);
            }
        } else if (formula instanceof LDLfTempOpTempFormula) {
            nestedLeft = ((LDLfTempOpTempFormula) formula).getRegExp();

            hasTest = checkForTestWithinStar(nestedLeft, hasStar);
            /* ignore checking goal formula, only regexp is of interest */
        } else {
            throw new IllegalArgumentException("Unknown formula type: " + formula);
        }

        return hasTest;
    }

    private static Automaton getElementaryAutomaton(Formula formula, boolean declare, PropositionalSignature ps) {
        Automaton automaton;
        State initialState;
        State endState;
        State falseState;

        automaton = new Automaton<>();

        Set<TransitionLabel> labels = AutomatonUtils.buildAllLables(declare, ps);

        if (formula instanceof LDLfttFormula) {
            initialState = automaton.addState(true, true);
            addLoopingTransitions(labels, initialState, initialState, automaton);
        } else if (formula instanceof LDLfffFormula) {
            initialState = automaton.addState(true, false);
            addLoopingTransitions(labels, initialState, initialState, automaton);
        }  else if (formula instanceof RegExpLocal){
            initialState = automaton.addState(true, false);
            endState = automaton.addState(false, true);
            falseState = automaton.addState(false, false);

            PropositionalFormula propFormula = ((RegExpLocal) formula).regExpLocal2Propositional();

            for (TransitionLabel label : labels) {
                Transition<TransitionLabel> transition;

                if (((PossibleWorld) label).satisfies(propFormula)) {
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
        } else {
            throw new IllegalArgumentException("Illegal elementary formula: " + formula);
        }

        automaton = new SinkComplete().transform(automaton);
        automaton = new Reducer<>().transform(automaton);

        return automaton;
    }


    /* ------ ldl2nfa compositional ------ */

    public static Automaton ldlf2nfaComp(boolean declare, LDLfFormula initialFormula, PropositionalSignature ps, long timeLimit) {
        long timeStarted = System.currentTimeMillis();

        // Automaton initialization: empty automaton
        QuotedFormulaStateFactory stateFactory = new QuotedFormulaStateFactory();
        Automaton automaton = new Automaton<>(stateFactory);
        stateFactory.setAutomaton(automaton);

        /*
        Algorithm data structures
         */
        LinkedList<QuotedFormulaState> toAnalyze = new LinkedList<>();

        /*
        Get all possible models for the signature and depending on the declare assumption.
         */
        Set<TransitionLabel> allLabels = AutomatonUtils.buildAllLables(declare, ps);

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
        AutomatonUtils.handleIfFinal(automaton, initialState, allLabels);

        // Add the initial state to the set of state to be analyzed
        toAnalyze.add(initialState);

        /*
        All transition loops in the false state
         */
        addLoopingTransitions(allLabels, falseState, falseState, automaton);

        // Cycle on states yet to be analyzed
        while (!toAnalyze.isEmpty() && ((System.currentTimeMillis() - timeStarted) < timeLimit)) {
            QuotedFormulaState currentState = toAnalyze.getFirst();

            /*
             Make conjunction of unquoted formula, stop if tests
             */
            Set<QuotedVar> formulaSet = currentState.getFormulaSet();
            LDLfFormula conjunctFormula;
            boolean hasTestWithinStar;

            Iterator<QuotedVar> i1 = formulaSet.iterator();

            if (formulaSet.size() > 0) {
                conjunctFormula = i1.next().getUnquotedFormula();
                hasTestWithinStar = checkForTestWithinStar(conjunctFormula);
            } else {
                throw new IllegalArgumentException("The set of quoted formula cannot be empty!");
            }

            while (i1.hasNext() && !hasTestWithinStar) {
                LDLfFormula varForm = i1.next().getUnquotedFormula();
                hasTestWithinStar = checkForTestWithinStar(varForm);
                conjunctFormula = new LDLfTempAndFormula(conjunctFormula, varForm);
            }

            /* if no tests within star do C-LDLf */
            if (!hasTestWithinStar) {
//                System.out.println("Creating C-LDLf automaton from " + conjunctFormula);
                Automaton comp = CompAutomatonUtils.LDLfToAutomaton(declare, conjunctFormula, ps, timeStarted, timeLimit);
                connectAutomatons(automaton, comp, currentState);
            } else {
                // Conjunction of the QuotedVar belonging to the current state
                QuotedFormula currentFormula = currentState.getQuotedConjunction();

                // For each possible label, call the delta function on currentFormula
                for (TransitionLabel label : allLabels) {
                    // All labels are PossibleWorldWrap which implement TransitionLabel
                    QuotedFormula deltaResult = currentFormula.delta(label);

                    // Compute the minimal interpretations satisfying deltaResult, that is, all the q'
                    Set<Set<QuotedVar>> newStateSetFormulas = deltaResult.getMinimalModels();

                    // newStateFormulas empty means that the current interpretation lead to the "false" state.
                    if (newStateSetFormulas.isEmpty()) {
                        // Add the transition (currentState, world, falseState)
                        Transition<TransitionLabel> t = new Transition<>(currentState, label, falseState);
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
                            QuotedFormulaState destinationState = AutomatonUtils.getStateIfExists(automaton, newStateFormulas);

                            if (destinationState == null) {
                                destinationState = (QuotedFormulaState) stateFactory.create(false, false, newStateFormulas);
                                AutomatonUtils.handleIfFinal(automaton, destinationState, allLabels);

                                // Add to the set of states to be analyzed only if it is not the true state!
                                if (!destinationState.getFormulaSet().isEmpty()) {
                                    toAnalyze.addLast(destinationState);
                                }
                            }

                            // Add the transition (currentState, world, destinationState)
                            Transition<TransitionLabel> t = new Transition<>(currentState, label, destinationState);
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
            }
            toAnalyze.remove(currentState);
        }

        return automaton;
    }

    private static void addLoopingTransitions(Set<TransitionLabel> labels, State from, State to, Automaton automaton) {
        for (TransitionLabel label : labels) {
            Transition<TransitionLabel> transition = new Transition<>(from, label, to);

            try {
                automaton.addTransition(transition);
            } catch (NoSuchStateException e) {
                e.printStackTrace();
            }
        }
    }

    /*
     * Connect comp to mainAutomaton using currentState as initial.
     */
    private static void connectAutomatons(Automaton mainAutomaton, Automaton comp, QuotedFormulaState currentState) {
        if (comp.initials().size() != 1) {
            throw new IllegalArgumentException("Connecting automata has more than 1 initial state: \n" + comp);
        }

        QuotedFormulaStateFactory stateFactory = (QuotedFormulaStateFactory) mainAutomaton.getStateFactory();
        HashMap<State, State> map = new HashMap<>();
        Iterator<State> i2 = comp.states().iterator();

        /*
        Add all states
         */
        while (i2.hasNext()) {
            State e = i2.next();
            State n;

            /*
            If e is an initial state, use currentState, otherwise create a new state
             */
            if (e.isInitial()) {
                currentState.setTerminal(e.isTerminal());
                map.put(e, currentState);
            } else {
                n = stateFactory.create(false, e.isTerminal(), null);
                map.put(e, n);
            }
        }

        /*
        Add all transitions
         */
        Iterator<Transition<TransitionLabel>> i3 = comp.delta().iterator();
        while (i3.hasNext()) {
            Transition<TransitionLabel> te = i3.next();
            Transition<TransitionLabel> tn = new Transition<>(map.get(te.start()), te.label(), map.get(te.end()));

            try {
                mainAutomaton.addTransition(tn);
            } catch (NoSuchStateException e) {
                e.printStackTrace();
            }
        }
    }

}
