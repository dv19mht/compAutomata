package main;

import formula.ldlf.LDLfFormula;
import formula.ldlf.LDLfTempAndFormula;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import rationals.Automaton;
import rationals.transformations.Mix;
import rationals.transformations.Reducer;
import utils.AutomatonUtils;
import utils.CompAutomatonUtils;

import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.Comparator;
import java.util.PriorityQueue;

public class PracticalValidityExperiment {

    public static void main(String[] args) {
        try (PrintWriter resultPrinter = new PrintWriter("prac_val.txt")){
            int input = Integer.parseInt(args[0]);
            resultPrinter.println("Algorithm;Constraints;total_time;constraint_time;states;transitions");
            for(int num = 1; num <= input; num++) {
                String temp;

                temp = ldlf2dfaGeneration(num);
                resultPrinter.println(temp);
                System.out.println();

//                ldlf2dfaGenerationAlt(num);
//                System.out.println();

                temp = compositionalGeneration(num);
                resultPrinter.println(temp);
                System.out.println();

//                temp = compositionalQueueGeneration(num);
//                resultPrinter.println(temp);
//                System.out.println();

                System.out.println("--------------------");
                System.out.println();
            }
        }
        catch (NumberFormatException | FileNotFoundException exception) {
            System.out.println("Invalid input format. Please insert an integer representing the maximum number of constraints to be generated. Thirty is the bound in the paper.");
        }

    }

    public static String ldlf2dfaGeneration(int num) {
        boolean declare = true;
        boolean minimize = true;
        boolean trim = false;
        boolean printing = false;

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

        return "ldlf2nfa;" + num + ";" + elapsedTime + ";" + timeConstraints + ";" + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size();
    }

    //Conjunction of formulae before automaton creation
    public static Automaton ldlf2dfaGenerationAlt(int num) {
        long startTime = System.currentTimeMillis();

        boolean declare = true;

        PropositionalSignature signature = generateSignatureInc(num);

        LDLfFormula conjunctionFormula = CompAutomatonUtils.stringToNnfLDLf("true");

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);
            LDLfFormula constraintFormula = CompAutomatonUtils.stringToNnfLDLf(currentConstraint);
            conjunctionFormula = new LDLfTempAndFormula(conjunctionFormula, constraintFormula);
        }

        Automaton mainAutomaton = AutomatonUtils.ldlf2Automaton(declare, conjunctionFormula, signature);

        long elapsedTime = System.currentTimeMillis() - startTime;
        System.out.println("Time for building the optimized ldl2dfa-automaton for "+ num +" activities is: " + elapsedTime + " ms");
        System.out.println("Automaton size = " + mainAutomaton.states().size() + " #states and " + mainAutomaton.delta().size() + " #transitions");

//        System.out.print("Running compliant trace... ");
//        List<String> complLog = generateCompliantLogInc(num);
//        //System.out.println(complLog);
//        runTrace(mainAutomaton, complLog);
//        //System.out.println();
//        System.out.print("Running uncompliant trace... ");
//        List<String> uncomplLog = generateUncompliantLogInc(num);
//        //System.out.println(uncomplLog);
//        runTrace(mainAutomaton, uncomplLog);

        return mainAutomaton;
    }

    public static String compositionalGeneration(int num) {
        boolean declare = true;

        PropositionalSignature signature = generateSignatureInc(num);

        LDLfFormula conjunctionFormula = CompAutomatonUtils.stringToNnfLDLf("true");

        long startTime = System.currentTimeMillis();
        long timeConstraints = 0;

        //Original implementation
        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, conjunctionFormula, signature);

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);
//            conjunctionFormula = new LDLfTempAndFormula(conjunctionFormula, constraintFormula);

            //Original implementation
            long constraintTimeStart = System.currentTimeMillis();
            LDLfFormula constraintFormula = CompAutomatonUtils.stringToNnfLDLf(currentConstraint);
            Automaton currentAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, constraintFormula, signature);
            timeConstraints += System.currentTimeMillis() - constraintTimeStart;

            mainAutomaton = new Mix<>().transform(mainAutomaton, currentAutomaton);
            mainAutomaton = new Reducer<>().transform(mainAutomaton);
        }

//        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, conjunctionFormula, signature);

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
        return "C-LDLf;" + num + ";" + elapsedTime + ";" + timeConstraints + ";"  + mainAutomaton.states().size() + ";" + mainAutomaton.delta().size();
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

//            currentAutomaton = new Reducer<>().transform(currentAutomaton); //Not necessary
            queue.add(currentAutomaton);
        }

        while (queue.size() > 1) {
            Automaton a1 = queue.poll();
            Automaton a2 = queue.poll();
            Automaton a3 = new Mix<>().transform(a1, a2);
            a3 = new Reducer<>().transform(a3); // Mem out if not used
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
