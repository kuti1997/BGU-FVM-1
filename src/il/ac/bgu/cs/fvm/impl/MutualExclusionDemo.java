package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.examples.PetersonProgramGraphBuilder;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedActDef;
import il.ac.bgu.cs.fvm.programgraph.ParserBasedCondDef;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.Pair;
import il.ac.bgu.cs.fvm.util.Util;
import il.ac.bgu.cs.fvm.verification.VerificationResult;
import il.ac.bgu.cs.fvm.verification.VerificationSucceeded;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import static il.ac.bgu.cs.fvm.util.CollectionHelper.seq;
import static il.ac.bgu.cs.fvm.util.CollectionHelper.set;

public class MutualExclusionDemo {

    private static FvmFacade fvm;

    public static void main(String[] args){
        System.out.println("Initialize the fvm instance.");
        fvm = FvmFacade.createInstance();


        System.out.println("Create & Interleave 2 Peterson program graphs.");
        ProgramGraph<Pair<String, String>, String> pg = fvm.interleave(PetersonProgramGraphBuilder.build(1), PetersonProgramGraphBuilder.build(2));

        System.out.println("Create transition system from the interleaved program graph.");
        TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts = fvm.transitionSystemFromProgramGraph(pg, set(new ParserBasedActDef()), set(new ParserBasedCondDef()));
        addLabels(ts);

        Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());

        System.out.println("Create automaton for mutex.");
        Automaton<String, String> mutexAutomaton = new Automaton<>();
        all.stream().filter(a -> !(a.contains("crit1") && a.contains("crit2"))).forEach(l -> mutexAutomaton.addTransition("q0", l, "q0"));
        all.stream().filter(a -> a.contains("crit1") && a.contains("crit2")).forEach(l -> mutexAutomaton.addTransition("q0", l, "q1"));
        all.forEach(l -> mutexAutomaton.addTransition("q1", l, "q1"));
        mutexAutomaton.setInitial("q0");
        mutexAutomaton.setAccepting("q1");

        System.out.println("Create automaton for starvation.");
        Automaton<String, String> starvationAutomaton = new Automaton<>();
        all.forEach(s -> starvationAutomaton.addTransition("q0", s, "q0"));
        all.stream().filter(s -> s.contains("wait1")).forEach(s -> starvationAutomaton.addTransition("q0", s, "q1"));
        all.stream().filter(s -> !s.contains("wait1") && !s.contains("crit1")).forEach(s -> starvationAutomaton.addTransition("q1", s, "q1"));
        all.stream().filter(s -> !s.contains("crit1") && !s.contains("crit1_enabled")).forEach(s -> starvationAutomaton.addTransition("q1", s, "q2"));
        all.stream().filter(s -> !s.contains("crit1") && !s.contains("crit1_enabled")).forEach(s -> starvationAutomaton.addTransition("q2", s, "q2"));
        starvationAutomaton.setInitial("q0");
        starvationAutomaton.setAccepting("q2");

        System.out.println("Verify omega regular property: Mutex");
        VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> mutexResult = fvm.verifyAnOmegaRegularProperty(ts, mutexAutomaton);
        System.out.println("Mutex verification " + (mutexResult instanceof VerificationSucceeded ? "succeeded!" : "failed!\n" + mutexResult.toString()));

        System.out.println("Verify omega regular property: Starvation");
        VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> starvationResult = fvm.verifyAnOmegaRegularProperty(ts, starvationAutomaton);
        System.out.println("Starvation verification " + (starvationResult instanceof VerificationSucceeded ? "succeeded!" : "failed!\n" + starvationResult.toString()));
    }


    private static void addLabels(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
        ts.getStates().forEach(st -> ts.getAtomicPropositions().forEach(ap -> ts.removeLabel(st, ap)));

        Set<String> aps = new HashSet<>(ts.getAtomicPropositions());
        aps.forEach(ts::removeAtomicProposition);

        seq("wait1", "wait2", "crit1", "crit2", "crit1_enabled").forEach(ts::addAtomicPropositions);

        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("crit1")).forEach(s -> ts.addToLabel(s, "crit1"));
        ts.getStates().stream().filter(s -> s.getFirst().getFirst().equals("wait1")).forEach(s -> ts.addToLabel(s, "wait1"));

        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("crit2")).forEach(s -> ts.addToLabel(s, "crit2"));
        ts.getStates().stream().filter(s -> s.getFirst().getSecond().equals("wait2")).forEach(s -> ts.addToLabel(s, "wait2"));

        Predicate<Pair<Pair<String, String>, ?>> _crit1 = ss -> ss.getFirst().getFirst().equals("crit1");
        ts.getStates().stream().filter(s -> fvm.post(ts, s).stream().anyMatch(_crit1)).forEach(s -> ts.addToLabel(s, "crit1_enabled"));
    }



}
