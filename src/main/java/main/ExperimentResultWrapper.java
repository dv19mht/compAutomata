package main;

import rationals.Automaton;

public class ExperimentResultWrapper {
    private String inputFormula;
    private String results;
    private Automaton automaton;
    private long timeSpent;

    public void setTimeSpent(long timeSpent) {
        this.timeSpent = timeSpent;
    }

    public void setInputFormula(String inputFormula) {
        this.inputFormula = inputFormula;
    }

    public void setAutomaton(Automaton automaton) {
        this.automaton = automaton;
    }

    public void setResults(String results) {
        this.results = results;
    }

    public String getInputFormula() {
        return inputFormula;
    }

    public Automaton getAutomaton() {
        return automaton;
    }

    public String getResults() {
        return results;
    }

    public long getTimeSpent() {
        return timeSpent;
    }
}
