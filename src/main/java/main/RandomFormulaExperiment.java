package main;

import formula.ldlf.LDLfFormula;
import formula.ltlf.LTLfFormula;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import rationals.Automaton;
import rationals.properties.ModelCheck;
import rationals.properties.isEmpty;
import utils.CompAutomatonUtils;
import utils.RandomFormulaGenerator;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.List;
import java.util.Random;

public class RandomFormulaExperiment {

    public static void main(String[] args) {
        try (PrintWriter resultPrinter = new PrintWriter("rand_form.txt")) {
            int lengths = Integer.parseInt(args[0]);
            int nProps = Integer.parseInt(args[1]);
            long timeLimit = Integer.parseInt(args[2]) * 1000L;
            long totalTimeStarted = System.currentTimeMillis();
            Random random = new Random();
            int nFormulaGenerated = 0;

            resultPrinter.println("algorithm;form_length;n_propositions;total_time;states;transitions;empty;formula");
            for(int len = 5; len <= lengths; len += 5) {
                for (int i = 0; i < 100; i++) { // number of formulas for each L (formula length)
                    for (int numProps = nProps; numProps <= nProps; numProps++) {
                        ExperimentResultWrapper ldlf2nfaResult;
                        ExperimentResultWrapper cldlfResult;
                        ExperimentResultWrapper top2cldlfResult;
                        random.setSeed(len + i);
                        RandomFormulaGenerator generator = new RandomFormulaGenerator(random);

                        List<Proposition> props = RandomFormulaGenerator.createPropositionList(nProps);
                        LTLfFormula ltl = generator.getRandomFormula(props, len, (double) 1 / 3);
//                        LTLfFormula ltl = generator.getRandomFormulaForG(props, len, (double) 1 / 3); // use F, G instead of U, R

                        System.out.println("i: " + i);
                        System.out.println("Formula " + ltl);
                        System.out.println();

                        ldlf2nfaResult = ldlf2dfaGeneration(len, numProps, props, ltl, timeLimit);
                        resultPrinter.println(ldlf2nfaResult.getResults());
                        System.out.println();

                        cldlfResult = cldlfGeneration(len, numProps, props, ltl, timeLimit);
                        resultPrinter.println(cldlfResult.getResults());
                        System.out.println();

                        top2cldlfResult = top2cldlfGeneration(len, numProps, props, ltl, timeLimit);
                        resultPrinter.println(top2cldlfResult.getResults());
                        System.out.println();

                        /* check containment both ways for C-LDLf */
                        modelCheckAutomata(timeLimit, ldlf2nfaResult, cldlfResult);
                        modelCheckAutomata(timeLimit, cldlfResult, ldlf2nfaResult);

                        /* check containment both ways for TOP-CLDLf */
                        modelCheckAutomata(timeLimit, ldlf2nfaResult, top2cldlfResult);
                        modelCheckAutomata(timeLimit, top2cldlfResult, ldlf2nfaResult);

                        nFormulaGenerated++;

                        System.out.println("--------------------");
                        System.out.println();
                    }
                }
            }
            System.out.println("Total test time was " + (System.currentTimeMillis() - totalTimeStarted));
            System.out.println("Formulae generated " + nFormulaGenerated);
        }
        catch (NumberFormatException | FileNotFoundException exception) {
            System.out.println(
                    "Invalid input format. " +
                    "Please insert an integer representing the maximum number of constraints to be generated. " +
                    "Thirty is the bound in the paper."
            );
        }
    }

    private static void modelCheckAutomata(long timeLimit, ExperimentResultWrapper a1Result, ExperimentResultWrapper a2Result) {
        ModelCheck modelCheck = new ModelCheck<>();
        Automaton a1 = a1Result.getAutomaton();
        Automaton a2 = a2Result.getAutomaton();

        if (modelCheck.test(a1, a2) && (bothEmpty(a1, a2) || bothNotEmpty(a1, a2))) {
            System.out.println("Formula OK ");
        } else {
            System.out.println("Formula NOT OK ");
            System.out.println(modelCheck.counterExamples());

            // If both are within time limit but not equal, stop
            if (a1Result.getTimeSpent() < timeLimit && a2Result.getTimeSpent() < timeLimit) {
                System.out.println("INTERRUPTED TEST");
                System.exit(1);
            }
        }
    }

    private static boolean bothNotEmpty(Automaton ldlf2nfa, Automaton cldlf) {
        return !(new isEmpty<>().test(ldlf2nfa)) && !(new isEmpty<>().test(cldlf));
    }

    private static boolean bothEmpty(Automaton ldlf2nfa, Automaton cldlf) {
        return new isEmpty<>().test(ldlf2nfa) && new isEmpty<>().test(cldlf);
    }

    public static ExperimentResultWrapper ldlf2dfaGeneration(int fLength, int nProps, List<Proposition> props, LTLfFormula formula, long timeLimit) {
        boolean declare = true;
        boolean minimize = true;
        boolean trim = false;
        boolean printing = false;
        ExperimentResultWrapper resultWrapper = new ExperimentResultWrapper();

        PropositionalSignature signature = new PropositionalSignature();
        signature.addAll(props);

        long startTime = System.currentTimeMillis();
        LTLfAutomatonResultWrapper mainAutomatonWrapper = Main.ltlfFormula2Aut(formula, signature, declare, minimize, trim, printing, timeLimit);
        Automaton mainAutomaton = mainAutomatonWrapper.getAutomaton();
        long elapsedTime = System.currentTimeMillis() - startTime;

//        mainAutomaton = new Reducer<>().transform(mainAutomaton);

        printResults(fLength, nProps, mainAutomaton, elapsedTime, "ldlf2nfa");
        boolean empty = new isEmpty<>().test(mainAutomaton);

        resultWrapper.setResults("ldlf2nfa;" + fLength + ";" + nProps + ";" + elapsedTime + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size() + ";" + empty + ";" + formula);
        resultWrapper.setAutomaton(mainAutomaton);
        resultWrapper.setInputFormula(formula.toString());
        resultWrapper.setTimeSpent(elapsedTime);

        return resultWrapper;
    }

    public static ExperimentResultWrapper cldlfGeneration(int fLength, int nProps, List<Proposition> props, LTLfFormula formula, long timeLimit) {
        boolean declare = true;
        ExperimentResultWrapper resultWrapper = new ExperimentResultWrapper();

        PropositionalSignature signature = new PropositionalSignature();
        signature.addAll(props);

        long startTime = System.currentTimeMillis();
        LDLfFormula ldl = formula.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, ldl, signature, startTime, timeLimit);
        long elapsedTime = System.currentTimeMillis() - startTime;

        printResults(fLength, nProps, mainAutomaton, elapsedTime, "C-LDLf");
        boolean empty = new isEmpty<>().test(mainAutomaton);

        resultWrapper.setResults("C-LDLf;" + fLength + ";" + nProps + ";" + elapsedTime + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size() + ";" + empty + ";" + formula);
        resultWrapper.setAutomaton(mainAutomaton);
        resultWrapper.setInputFormula(formula.toString());
        resultWrapper.setTimeSpent(elapsedTime);

        return resultWrapper;
    }

    public static ExperimentResultWrapper top2cldlfGeneration(int fLength, int nProps, List<Proposition> props, LTLfFormula formula, long timeLimit) {
        boolean declare = true;
        ExperimentResultWrapper resultWrapper = new ExperimentResultWrapper();

        PropositionalSignature signature = new PropositionalSignature();
        signature.addAll(props);

        long startTime = System.currentTimeMillis();
        LDLfFormula ldl = formula.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        Automaton mainAutomaton = CompAutomatonUtils.ldlf2nfaComp(declare, ldl, signature, timeLimit);
        long elapsedTime = System.currentTimeMillis() - startTime;

        printResults(fLength, nProps, mainAutomaton, elapsedTime, "TOP-CLDLf");
        boolean empty = new isEmpty<>().test(mainAutomaton);

        resultWrapper.setResults("TOP-CLDLf;" + fLength + ";" + nProps + ";" + elapsedTime + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size() + ";" + empty + ";" + formula);
        resultWrapper.setAutomaton(mainAutomaton);
        resultWrapper.setInputFormula(formula.toString());
        resultWrapper.setTimeSpent(elapsedTime);

        return resultWrapper;
    }

    private static void printResults(int length, int nProps, Automaton mainAutomaton, long elapsedTime, String type) {
        System.out.println("Time for building the optimized " + type + " automaton for formula length " + length + " with " + nProps + " props is: " + elapsedTime + " ms");
        System.out.println("Automaton size = " + mainAutomaton.states().size() + " #states and " + mainAutomaton.delta().size() + " #transitions");
        if (new isEmpty<>().test(mainAutomaton)) {
            System.out.println("Automaton was EMPTY");
        }
    }

}
