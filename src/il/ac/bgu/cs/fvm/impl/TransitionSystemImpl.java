package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.*;
import il.ac.bgu.cs.fvm.transitionsystem.Transition;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Created by Tal on 17/11/2017.
 */
public class TransitionSystemImpl<S, A, P> implements TransitionSystem<S, A, P> {
    private String name;
    private Set<S> states;
    private Set<S> iStates;
    private Set<A> actions;
    private Set<Transition<S, A>> transitions;
    private Set<P> atomicPropositions;
    private Map<S, Set<P>> labels;

    public TransitionSystemImpl(){
        name = "";
        states = new HashSet<>();
        iStates = new HashSet<>();
        actions = new HashSet<>();
        transitions = new HashSet<>();
        atomicPropositions = new HashSet<>();
        labels = new HashMap<>();
        states.forEach(s -> labels.put(s, new HashSet<>()));
    }

    @Override
    public String getName() {
        return name;

    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public void addAction(A a) {
        actions.add(a);
    }

    @Override
    public void addInitialState(S s) throws FVMException {
        if(!states.contains(s)){
            throw new InvalidInitialStateException(s);
        }
        iStates.add(s);
    }

    @Override
    public void addState(S s) {
        states.add(s);
        labels.put(s, new HashSet<>());
    }

    @Override
    public void addTransition(Transition<S, A> t) throws FVMException {
        if(!states.contains(t.getFrom()) || !actions.contains(t.getAction()) || !states.contains(t.getTo())){
            throw new InvalidTransitionException(t);
        }
        transitions.add(t);
    }

    @Override
    public Set<A> getActions() {
        return actions;
    }

    @Override
    public void addAtomicProposition(P p) {
        atomicPropositions.add(p);
    }

    @Override
    public Set<P> getAtomicPropositions() {
        return atomicPropositions;
    }

    @Override
    public void addToLabel(S s, P l) throws FVMException {
        if(!states.contains(s) || !atomicPropositions.contains(l)){
            throw new InvalidLablingPairException(s, l);
        }
        labels.get(s).add(l);
    }

    @Override
    public Set<P> getLabel(S s) {
        if(!states.contains(s)){
            throw new StateNotFoundException(s);
        }
        return labels.get(s);
    }

    @Override
    public Set<S> getInitialStates() {
        return iStates;
    }

    @Override
    public Map<S, Set<P>> getLabelingFunction() {
        return labels;
    }

    @Override
    public Set<S> getStates() {
        return states;
    }

    @Override
    public Set<Transition<S, A>> getTransitions() {
        return transitions;
    }

    @Override
    public void removeAction(A a) throws FVMException {
        if(transitions.stream().anyMatch(t -> t.getAction().equals(a))){
            throw new DeletionOfAttachedActionException(a, TransitionSystemPart.TRANSITIONS);
        }
        actions.remove(a);
    }

    @Override
    public void removeAtomicProposition(P p) throws FVMException {
        if(labels.values().stream().anyMatch(s -> s.contains(p))){
            throw new DeletionOfAttachedAtomicPropositionException(p, TransitionSystemPart.LABELING_FUNCTION);
        }
        atomicPropositions.remove(p);
    }

    @Override
    public void removeInitialState(S s) {
        iStates.remove(s);
    }

    @Override
    public void removeLabel(S s, P l) {
        labels.get(s).remove(l);
    }

    @Override
    public void removeState(S s) throws FVMException {
        if(iStates.contains(s)){
            throw new DeletionOfAttachedStateException(s, TransitionSystemPart.INITIAL_STATES);
        } if(transitions.stream().anyMatch(t -> t.getFrom().equals(s) || t.getTo().equals(s))){
            throw new DeletionOfAttachedStateException(s, TransitionSystemPart.TRANSITIONS);
        } if (labels.get(s).size() > 0) {
          throw new DeletionOfAttachedStateException(s, TransitionSystemPart.LABELING_FUNCTION);
        }

        labels.remove(s);
        states.remove(s);
    }

    @Override
    public void removeTransition(Transition<S, A> t) {
        transitions.remove(t);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TransitionSystemImpl<?, ?, ?> that = (TransitionSystemImpl<?, ?, ?>) o;

        return name.equals(that.name) &&
                states.equals(that.states) &&
                iStates.equals(that.iStates) &&
                actions.equals(that.actions) &&
                transitions.equals(that.transitions) &&
                atomicPropositions.equals(that.atomicPropositions) &&
                labels.equals(that.labels);
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + states.hashCode();
        result = 31 * result + iStates.hashCode();
        result = 31 * result + actions.hashCode();
        result = 31 * result + transitions.hashCode();
        result = 31 * result + atomicPropositions.hashCode();
        result = 31 * result + labels.hashCode();
        return result;
    }
}
