package main;

import formula.ldlf.LDLfFormula;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import rationals.Automaton;
import rationals.transformations.Mix;
import rationals.transformations.Reducer;
import utils.CompAutomatonUtils;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.Comparator;
import java.util.PriorityQueue;

/**
 * @author Mathias Hedqvist 2022-06-03
 */
public class PracticalValidityExperiment {

    public static void main(String[] args) {
        try (PrintWriter resultPrinter = new PrintWriter("prac_val.txt")){
            int input = Integer.parseInt(args[0]);
            resultPrinter.println("Algorithm;Constraints;total_time;constraint_time;states;transitions");
            for(int num = 1; num <= input; num++) {
                ExperimentResultWrapper ldlf2nfaResult;
                ExperimentResultWrapper cldlfResult;

                ldlf2nfaResult = ldlf2nfaGeneration(num);
                resultPrinter.println(ldlf2nfaResult.getResults());
                System.out.println();

                cldlfResult = cldlfGeneration(num);
                resultPrinter.println(cldlfResult.getResults());
                System.out.println();

//                temp = compositionalQueueGeneration(num);
//                resultPrinter.println(temp);
//                System.out.println();

                /* check containment both ways for C-LDLf */
                RandomFormulaExperiment.modelCheckAutomata(Long.MAX_VALUE, ldlf2nfaResult, cldlfResult);
                RandomFormulaExperiment.modelCheckAutomata(Long.MAX_VALUE, cldlfResult, ldlf2nfaResult);

                System.out.println("--------------------");
                System.out.println();
            }
        }
        catch (NumberFormatException | FileNotFoundException exception) {
            System.out.println("Invalid input format. Please insert an integer representing the maximum number of constraints to be generated. Thirty is the bound in the paper.");
        }

    }

    public static ExperimentResultWrapper ldlf2nfaGeneration(int num) {
        boolean declare = true;
        boolean minimize = true;
        boolean trim = false;
        boolean printing = false;
        ExperimentResultWrapper resultWrapper = new ExperimentResultWrapper();

        PropositionalSignature signature = generateSignatureInc(num);

        LTLfAutomatonResultWrapper mainAutomatonWrapper = Main.ltlfString2Aut("true", signature, declare, minimize, trim, printing);
        Automaton mainAutomaton = mainAutomatonWrapper.getAutomaton();

        long startTime = System.currentTimeMillis();
        long timeConstraints = 0;

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);

            long constraintTimeStart = System.currentTimeMillis();
            LTLfAutomatonResultWrapper currentAutomatonWrapper = Main.ltlfString2Aut(currentConstraint, signature, declare, minimize, trim, printing);
            Automaton currentAutomaton = currentAutomatonWrapper.getAutomaton();
            timeConstraints += System.currentTimeMillis() - constraintTimeStart;

            mainAutomaton = new Mix<>().transform(mainAutomaton, currentAutomaton);
            mainAutomaton = new Reducer<>().transform(mainAutomaton);
        }

        long elapsedTime = System.currentTimeMillis() - startTime;
        double timeConstraintRatio = (double) timeConstraints / elapsedTime;
        timeConstraintRatio = Math.round(timeConstraintRatio * 100);

        printResults(num, timeConstraints, mainAutomaton, elapsedTime, timeConstraintRatio, "ldlf2nfa");

//        System.out.print("Running compliant trace... ");
//        List<String> complLog = generateCompliantLogInc(num);
//        //System.out.println(complLog);
//        runTrace(mainAutomaton, complLog);
//        //System.out.println();
//        System.out.print("Running uncompliant trace... ");
//        List<String> uncomplLog = generateUncompliantLogInc(num);
//        //System.out.println(uncomplLog);
//        runTrace(mainAutomaton, uncomplLog);

        resultWrapper.setResults("ldlf2nfa;" + num + ";" + elapsedTime + ";" + timeConstraints + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size());
        resultWrapper.setAutomaton(mainAutomaton);
        resultWrapper.setTimeSpent(elapsedTime);

        return resultWrapper;
    }

    public static ExperimentResultWrapper cldlfGeneration(int num) {
        boolean declare = true;
        ExperimentResultWrapper resultWrapper = new ExperimentResultWrapper();

        PropositionalSignature signature = generateSignatureInc(num);

        LDLfFormula conjunctionFormula = CompAutomatonUtils.stringToNnfLDLf("true");

        long startTime = System.currentTimeMillis();
        long timeConstraints = 0;

        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, conjunctionFormula, signature);

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);

            long constraintTimeStart = System.currentTimeMillis();
            LDLfFormula constraintFormula = CompAutomatonUtils.stringToNnfLDLf(currentConstraint);
            Automaton currentAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, constraintFormula, signature);
            timeConstraints += System.currentTimeMillis() - constraintTimeStart;

            mainAutomaton = new Mix<>().transform(mainAutomaton, currentAutomaton);
            mainAutomaton = new Reducer<>().transform(mainAutomaton);
        }

        long elapsedTime = System.currentTimeMillis() - startTime;
        double timeConstraintRatio = (double) timeConstraints / elapsedTime;
        timeConstraintRatio = Math.round(timeConstraintRatio * 100);

        printResults(num, timeConstraints, mainAutomaton, elapsedTime, timeConstraintRatio, "C-LDLf");

//        System.out.print("Running compliant trace... ");
//        List<String> complLog = generateCompliantLogInc(num);
//        //System.out.println(complLog);
//        runTrace(mainAutomaton, complLog);
//        //System.out.println();
//        System.out.print("Running uncompliant trace... ");
//        List<String> uncomplLog = generateUncompliantLogInc(num);
//        //System.out.println(uncomplLog);
//        runTrace(mainAutomaton, uncomplLog);

        resultWrapper.setResults("C-LDLf;" + num + ";" + elapsedTime + ";" + timeConstraints + ";"  + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size());
        resultWrapper.setAutomaton(mainAutomaton);
        resultWrapper.setTimeSpent(elapsedTime);

        return resultWrapper;
    }

    /* Uses a priority queue to combine automata */
    public static String compositionalQueueGeneration(int num) {
        boolean declare = true;

        PropositionalSignature signature = generateSignatureInc(num);

        long startTime = System.currentTimeMillis();
        long timeConstraints = 0;

        PriorityQueue<Automaton> queue = new PriorityQueue<>(Comparator.comparingInt(a -> a.states().size()));

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);

            long constraintTimeStart = System.currentTimeMillis();
            LDLfFormula constraintFormula = CompAutomatonUtils.stringToNnfLDLf(currentConstraint);
            Automaton currentAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, constraintFormula, signature);
            timeConstraints += System.currentTimeMillis() - constraintTimeStart;

            queue.add(currentAutomaton);
        }

        while (queue.size() > 1) {
            Automaton a1 = queue.poll();
            Automaton a2 = queue.poll();
            Automaton a3 = new Mix<>().transform(a1, a2);
            a3 = new Reducer<>().transform(a3);
            queue.add(a3);
        }
        Automaton mainAutomaton = queue.poll();

        long elapsedTime = System.currentTimeMillis() - startTime;
        double timeConstraintRatio = (double) timeConstraints / elapsedTime;
        timeConstraintRatio = Math.round(timeConstraintRatio * 100);

        printResults(num, timeConstraints, mainAutomaton, elapsedTime, timeConstraintRatio, "C-LDLfQueue");

//        System.out.print("Running compliant trace... ");
//        List<String> complLog = generateCompliantLogInc(num);
//        //System.out.println(complLog);
//        runTrace(mainAutomaton, complLog);
//        //System.out.println();
//        System.out.print("Running uncompliant trace... ");
//        List<String> uncomplLog = generateUncompliantLogInc(num);
//        //System.out.println(uncomplLog);
//        runTrace(mainAutomaton, uncomplLog);
        return "C-LDLfQueue;" + num + ";" + elapsedTime + ";" + timeConstraints + ";"  + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size();
    }

    private static void printResults(int num, long timeConstraints, Automaton mainAutomaton, long elapsedTime, double timeConstraintRatio, String type) {
        System.out.println("Time for building the optimized " + type + " automaton for "+ num +" activities is: " + elapsedTime + " ms");
        System.out.println("Automaton size = " + mainAutomaton.states().size() + " #states and " + mainAutomaton.delta().size() + " #transitions");
        System.out.println("Time spent on constraint formulae: " + timeConstraints + " (" + timeConstraintRatio + "%)");
    }

    public static PropositionalSignature generateSignatureInc(int num) {
        int currIter = Math.floorDiv(num, 11);

        PropositionalSignature signature = new PropositionalSignature();
        int i=0;
        do {
            Proposition lt = new Proposition("lt" + i); //0
            Proposition re = new Proposition("re" + i); //1
            Proposition fha = new Proposition("fha" + i); //2
            Proposition ps = new Proposition("ps" + i); //3
            Proposition os = new Proposition("os" + i); //4 //inc
            Proposition o = new Proposition("o" + i); //5 //inc
            Proposition iht = new Proposition("iht" + i); //6 //inc
            Proposition he = new Proposition("he" + i); //7 //inc
            Proposition n = new Proposition("n" + i); //8 //inc
            Proposition fu = new Proposition("fu" + i); //9
            Proposition fhaNext = new Proposition("fha" + (i + 1)); //10

            signature.add(lt);
            signature.add(re);
            signature.add(fha);
            signature.add(ps);
            signature.add(os);
            signature.add(o);
            signature.add(iht);
            signature.add(he);
            signature.add(n);
            signature.add(fu);
            signature.add(fhaNext);

            i++;
        } while(i<=currIter);

        return signature;
    }

    public static String getConstraint(int num) {
        String[] constraints = new String[14];

        int currIter = Math.floorDiv(num, 14);
        int currConstraint = num % 14;

        constraints[0] = "( (!fha"+currIter+" ) U re"+currIter+" ) || ( G(!fha"+currIter+") )"; //RE_TEST
        constraints[1] = "( (!fha"+currIter+") U lt"+currIter+" ) || ( G(!fha"+currIter+") )"; //RE_TEST
        constraints[2] = "( (!ps"+currIter+") U fha"+currIter+" ) || ( G(!ps"+currIter+") )"; //RE_TEST
        constraints[3] = "( (!os"+currIter+") U ps"+currIter+" ) || ( G(!os"+currIter+") )"; //RE_TEST
        constraints[4] = "( (!o"+currIter+") U ps"+currIter+" ) || ( G(!o"+currIter+") )"; //RE_TEST
        constraints[5] = "( (!iht"+currIter+") U ps"+currIter+" ) || ( G(!iht"+currIter+") )"; //RE_TEST

        constraints[6] = "((F os"+currIter+") || (F o"+currIter+")) && (!( (F os"+currIter+") && (F o"+currIter+") ))";

        constraints[7] = "(F iht"+currIter+") -> (F o"+currIter+")";
        constraints[8] = "(F he"+currIter+") -> (F o"+currIter+")";

        constraints[9] = "G(os"+currIter+" -> (X (F n"+currIter+") ) )";
        constraints[10] = "G(o"+currIter+" -> (X (F n"+currIter+") ) )";
        constraints[11] = "G(iht"+currIter+" -> (X (F n"+currIter+") ) )";

        constraints[12] = "( G(n"+currIter+" -> (X (F fu"+currIter+"))) ) && ( ( (!fu"+currIter+") U n"+currIter+") || (G (!fu"+currIter+")))"; //RE_TEST

        constraints[13] = "( ( (!fha"+(currIter+1)+") U fu"+(currIter)+" ) || (G (!fha"+(currIter+1)+" )))"; //RE_TEST

        //System.out.println(constraints[currConstraint]);
        return constraints[currConstraint];
    }

}
