package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.exceptions.FVMException;
import il.ac.bgu.cs.fvm.programgraph.PGTransition;
import il.ac.bgu.cs.fvm.programgraph.ProgramGraph;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Created by Tal on 08/12/2017.
 */
public class ProgramGraphImpl<L, A> implements ProgramGraph<L, A> {
    private String name;
    private Set<List<String>> init;

    private Set<L> loc;
    private Set<L> loc0;
    private Set<PGTransition<L, A>> trans;

    ProgramGraphImpl(){
        name = "Program Graph";
        init = new HashSet<>();
        loc = new HashSet<>();
        loc0 = new HashSet<>();
        trans = new HashSet<>();

    }

    @Override
    public void addInitalization(List<String> init) {
        this.init.add(init);
    }

    @Override
    public void addInitialLocation(L location) {
        if(!loc.contains(location)){
            throw new FVMException("Invalid initial state");
        }
        loc0.add(location);
    }

    @Override
    public void addLocation(L l) {
        loc.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
        if(!loc.contains(t.getFrom()) || !loc.contains(t.getTo())){
            throw new FVMException("Invalid transition");
        }
        trans.add(t);
    }

    @Override
    public Set<List<String>> getInitalizations() {
        return init;
    }

    @Override
    public Set<L> getInitialLocations() {
        return loc0;
    }

    @Override
    public Set<L> getLocations() {
        return loc;
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public Set<PGTransition<L, A>> getTransitions() {
        return trans;
    }

    @Override
    public void removeLocation(L l) {
        if(trans.stream().anyMatch(t -> t.getFrom().equals(l) || t.getTo().equals(l))){
            throw new FVMException("Unable to remove location.");
        }
        loc0.remove(l);
        loc.remove(l);
    }

    @Override
    public void removeTransition(PGTransition<L, A> t) {
        trans.remove(t);
    }

    @Override
    public void setName(String name) {
        this.name = name;
    }

    @Override
    public String toString() {
        return "ProgramGraphImpl{" +
                "name='" + name + '\'' +
                ", init=" + init +
                ", loc=" + loc +
                ", loc0=" + loc0 +
                ", trans=" + trans +
                '}';
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ProgramGraphImpl<?, ?> that = (ProgramGraphImpl<?, ?>) o;

        return name.equals(that.name) && init.equals(that.init) && loc.equals(that.loc) && loc0.equals(that.loc0) && trans.equals(that.trans);
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + init.hashCode();
        result = 31 * result + loc.hashCode();
        result = 31 * result + loc0.hashCode();
        result = 31 * result + trans.hashCode();
        return result;
    }
}
