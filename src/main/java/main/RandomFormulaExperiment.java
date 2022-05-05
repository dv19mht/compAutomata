package main;

import formula.ldlf.LDLfFormula;
import formula.ltlf.LTLfFormula;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import rationals.Automaton;
import rationals.properties.isEmpty;
import rationals.transformations.Reducer;
import rationals.transformations.SinkComplete;
import utils.CompAutomatonUtils;
import utils.RandomFormulaGenerator;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.List;
import java.util.Random;

public class RandomFormulaExperiment {

    public static void main(String[] args) {
        try (PrintWriter resultPrinter = new PrintWriter("rand_form.txt")){
            int length = Integer.parseInt(args[0]);
            int nProps = Integer.parseInt(args[1]);
            long timeLimit = Integer.parseInt(args[2]) * 1000L;
            Random random = new Random();

            resultPrinter.println("algorithm;form_length;n_propositions;total_time;states;transitions;empty;formula");
            for(int num = 5; num <= length; num += 5) {
                for (int numProps = nProps; numProps <= nProps; numProps++) {
                    String temp;
                    random.setSeed(num);
                    RandomFormulaGenerator generator = new RandomFormulaGenerator(random);

                    List<Proposition> props = RandomFormulaGenerator.createPropositionList(nProps);
//                    LTLfFormula ltl = generator.getRandomFormula(props, num, (double) 1 / 3);
                    LTLfFormula ltl = generator.getRandomFormulaForG(props, num, (double) 1 / 2);

                    temp = ldlf2dfaGeneration(num, numProps, props, ltl, timeLimit);
                    resultPrinter.println(temp);
                    System.out.println();

                    temp = compositionalGeneration(num, numProps, props, ltl, timeLimit);
                    resultPrinter.println(temp);
                    System.out.println();

                    System.out.println("--------------------");
                    System.out.println();
                }
            }
        }
        catch (NumberFormatException | FileNotFoundException exception) {
            System.out.println("Invalid input format. " +
                    "Please insert an integer representing the maximum number of constraints to be generated. " +
                    "Thirty is the bound in the paper.");
        }
    }

    public static String ldlf2dfaGeneration(int fLength, int nProps, List<Proposition> props, LTLfFormula formula, long timeLimit) {
        boolean declare = true;
        boolean minimize = true;
        boolean trim = false;
        boolean printing = false;

        PropositionalSignature signature = new PropositionalSignature();
        signature.addAll(props);

        long startTime = System.currentTimeMillis();
        LTLfAutomatonResultWrapper mainAutomatonWrapper = Main.ltlfFormula2Aut(formula, signature, declare, minimize, trim, printing, timeLimit);
        Automaton mainAutomaton = mainAutomatonWrapper.getAutomaton();
        long elapsedTime = System.currentTimeMillis() - startTime;

        mainAutomaton = new Reducer<>().transform(mainAutomaton);

        printResults(fLength, nProps, mainAutomaton, elapsedTime, "ldlf2nfa");
        boolean empty = new isEmpty<>().test(mainAutomaton);

        return "ldlf2nfa;" + fLength + ";" + nProps + ";" + elapsedTime + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size() + ";" + empty + ";" + formula;
    }

    public static String compositionalGeneration(int fLength, int nProps, List<Proposition> props, LTLfFormula formula, long timeLimit) {
        boolean declare = true;

        PropositionalSignature signature = new PropositionalSignature();
        signature.addAll(props);

        long startTime = System.currentTimeMillis();
        LDLfFormula ldl = formula.toLDLf();
        ldl = (LDLfFormula) ldl.nnf();
        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, ldl, signature, startTime, timeLimit);
        long elapsedTime = System.currentTimeMillis() - startTime;

        mainAutomaton = new SinkComplete().transform(mainAutomaton);

        printResults(fLength, nProps, mainAutomaton, elapsedTime, "C-LDLf");
        boolean empty = new isEmpty<>().test(mainAutomaton);

        return "C-LDLf;" + fLength + ";" + nProps + ";" + elapsedTime + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size() + ";" + empty + ";" + formula;
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
