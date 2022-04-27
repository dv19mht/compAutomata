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

import java.util.Comparator;
import java.util.PriorityQueue;

public class CompLDLfExperiment {

    public static void main(String[] args) {
        try {
            int input = Integer.parseInt(args[0]);
            for(int num=14; num<input; num++) {
//                ldlf2dfaGeneration(num);
//                System.out.println();
//                ldlf2dfaGenerationAlt(num);
//                System.out.println();
                compositionGeneration(num);
                System.out.println();
//                compositionGenerationQueue(num);
//                System.out.println();
                System.out.println("--------------------");
                System.out.println();
            }
        }
        catch (NumberFormatException exception) {
            System.out.println("Invalid input format. Please insert an integer representing the maximum number of constraints to be generated. Thirty is the bound in the paper.");
        }
    }

    public static Automaton ldlf2dfaGeneration(int num) {
        long startTime = System.currentTimeMillis();

        boolean declare = true;
        boolean minimize = true;
        boolean trim = false;
        boolean printing = false;

        PropositionalSignature signature = generateSignatureInc(num);

        //Original implementation
        LTLfAutomatonResultWrapper mainAutomatonWrapper = Main.ltlfString2Aut("true", signature, declare, minimize, trim, printing);
        Automaton mainAutomaton = mainAutomatonWrapper.getAutomaton();

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);

            //Original implementation
            LTLfAutomatonResultWrapper currentAutomatonWrapper = Main.ltlfString2Aut(currentConstraint, signature, declare, minimize, trim, printing);
            Automaton currentAutomaton = currentAutomatonWrapper.getAutomaton();
            mainAutomaton = new Mix<>().transform(mainAutomaton, currentAutomaton);
            mainAutomaton = new Reducer<>().transform(mainAutomaton);
        }

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

    public static Automaton ldlf2dfaGenerationAlt(int num) {
        long startTime = System.currentTimeMillis();

        boolean declare = true;

        PropositionalSignature signature = generateSignatureInc(num);

        //Conjunction before automaton creation
        LDLfFormula conjunctionFormula = CompAutomatonUtils.stringToNnfLDLf("true");

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);

            //Conjugation before automaton creation
            LDLfFormula constraintFormula = CompAutomatonUtils.stringToNnfLDLf(currentConstraint);
            conjunctionFormula = new LDLfTempAndFormula(conjunctionFormula, constraintFormula);
        }

        //Conjunction before automaton creation
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

    public static Automaton compositionGeneration(int num) {

        long startTime = System.currentTimeMillis();

        boolean declare = true;

        PropositionalSignature signature = generateSignatureInc(num);

        LDLfFormula conjunctionFormula = CompAutomatonUtils.stringToNnfLDLf("true");

        //Original implementation
//        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, conjunctionFormula, signature);

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);
            LDLfFormula constraintFormula = CompAutomatonUtils.stringToNnfLDLf(currentConstraint);
            conjunctionFormula = new LDLfTempAndFormula(conjunctionFormula, constraintFormula);

            //Original implementation
//            Automaton currentAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, constraintFormula, signature);
//            mainAutomaton = new Mix<>().transform(mainAutomaton, currentAutomaton);
//            mainAutomaton = new Reducer<>().transform(mainAutomaton);
        }

        Automaton mainAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, conjunctionFormula, signature);

        long elapsedTime = System.currentTimeMillis() - startTime;
        System.out.println("Time for building the optimized compositional automaton for "+ num +" activities is: " + elapsedTime + " ms");
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

    public static Automaton compositionGenerationQueue(int num) {

        long startTime = System.currentTimeMillis();

        boolean declare = true;

        PropositionalSignature signature = generateSignatureInc(num);

        //Queue implementation
        PriorityQueue<Automaton> queue = new PriorityQueue<>(Comparator.comparingInt(a -> a.states().size()));

        for (int i=0; i<num; i++) {
            String currentConstraint = getConstraint(i);
            LDLfFormula constraintFormula = CompAutomatonUtils.stringToNnfLDLf(currentConstraint);

            //Queue implementation
            Automaton currentAutomaton = CompAutomatonUtils.LDLfToAutomaton(declare, constraintFormula, signature);
            currentAutomaton = new Reducer<>().transform(currentAutomaton);
            queue.add(currentAutomaton);
        }

        //Queue implementation
        while (queue.size() > 1) {
            Automaton a1 = queue.poll();
            Automaton a2 = queue.poll();
            Automaton a3 = new Mix<>().transform(a1, a2);
            a3 = new Reducer<>().transform(a3); // Mem out if not used
            queue.add(a3);
        }
        Automaton mainAutomaton = queue.poll();

        long elapsedTime = System.currentTimeMillis() - startTime;
        System.out.println("Time for building the optimized compositional automaton for "+ num +" activities is: " + elapsedTime + " ms");
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
