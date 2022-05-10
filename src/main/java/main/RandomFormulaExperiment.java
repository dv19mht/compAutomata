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

// 25 26 100 293s FG

public class RandomFormulaExperiment {

    public static void main(String[] args) {
        try (PrintWriter resultPrinter = new PrintWriter("rand_form.txt")){
            int lengths = Integer.parseInt(args[0]);
            int nProps = Integer.parseInt(args[1]);
            long timeLimit = Integer.parseInt(args[2]) * 1000L;
            long totalTimeStarted = System.currentTimeMillis();
            Random random = new Random();
            int nFormulaGenerated = 0;
            int nFormulaVerified = 0;

            resultPrinter.println("algorithm;form_length;n_propositions;total_time;states;transitions;empty;formula");
            for(int len = 5; len <= lengths; len += 5) {
                for (int i = 0; i < 10; i++) { // number of formulas for each L (formula length)
                    for (int numProps = nProps; numProps <= nProps; numProps++) {
                        ExperimentResultWrapper ldlf2nfaResult;
                        ExperimentResultWrapper cldlfResult;
                        random.setSeed(len + i);
                        RandomFormulaGenerator generator = new RandomFormulaGenerator(random);

                        List<Proposition> props = RandomFormulaGenerator.createPropositionList(nProps);
                        LTLfFormula ltl = generator.getRandomFormula(props, len, (double) 1 / 3);
//                        LTLfFormula ltl = generator.getRandomFormulaForG(props, len, (double) 1 / 3);

                        ldlf2nfaResult = ldlf2dfaGeneration(len, numProps, props, ltl, timeLimit);
                        resultPrinter.println(ldlf2nfaResult.getResults());
                        System.out.println();

                        cldlfResult = compositionalGeneration(len, numProps, props, ltl, timeLimit);
                        resultPrinter.println(cldlfResult.getResults());
                        System.out.println();

                        ModelCheck modelCheck = new ModelCheck<>();
                        Automaton ldlf2nfa = ldlf2nfaResult.getAutomaton();
                        Automaton cldlf = cldlfResult.getAutomaton();

                        if (modelCheck.test(ldlf2nfaResult.getAutomaton(), cldlfResult.getAutomaton()) &&
                                (bothEmpty(ldlf2nfa, cldlf) || bothNotEmpty(ldlf2nfa, cldlf))) {
                            System.out.println("Formula OK " + ltl);
                            nFormulaVerified++;
                        } else {
                            System.out.println("Formula NOT OK " + ltl);
                            System.out.println(modelCheck.counterExamples());
                            System.exit(1);
                        }
                        nFormulaGenerated++;

                        System.out.println("--------------------");
                        System.out.println();
                    }
                }
            }
            System.out.println("Total test time was " + (System.currentTimeMillis() - totalTimeStarted));
            System.out.println("Verified formula " + nFormulaVerified + "/" + nFormulaGenerated);
        }
        catch (NumberFormatException | FileNotFoundException exception) {
            System.out.println("Invalid input format. " +
                    "Please insert an integer representing the maximum number of constraints to be generated. " +
                    "Thirty is the bound in the paper.");
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

        return resultWrapper;
    }

    public static ExperimentResultWrapper compositionalGeneration(int fLength, int nProps, List<Proposition> props, LTLfFormula formula, long timeLimit) {
        boolean declare = true;
        ExperimentResultWrapper resultWrapper = new ExperimentResultWrapper();

        PropositionalSignature signature = new PropositionalSignature();
        signature.addAll(props);

        long startTime = System.currentTimeMillis();
        LDLfFormula ldl = formula.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, ldl, signature, startTime, timeLimit);
        long elapsedTime = System.currentTimeMillis() - startTime;

//        mainAutomaton = new SinkComplete().transform(mainAutomaton);

        printResults(fLength, nProps, mainAutomaton, elapsedTime, "C-LDLf");
        boolean empty = new isEmpty<>().test(mainAutomaton);

        resultWrapper.setResults("C-LDLf;" + fLength + ";" + nProps + ";" + elapsedTime + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size() + ";" + empty + ";" + formula);
        resultWrapper.setAutomaton(mainAutomaton);
        resultWrapper.setInputFormula(formula.toString());

        return resultWrapper;
    }

    private static void printResults(int length, int nProps, Automaton mainAutomaton, long elapsedTime, String type) {
        System.out.println("Time for building the optimized " + type + " automaton for formula length " + length + " with " + nProps + " props is: " + elapsedTime + " ms");
        System.out.println("Automaton size = " + mainAutomaton.states().size() + " #states and " + mainAutomaton.delta().size() + " #transitions");
        if (new isEmpty<>().test(mainAutomaton)) {
            System.out.println("Automaton was EMPTY");
        } else {
//            System.out.println(mainAutomaton);
        }
    }
}
