package il.ac.bgu.cs.fvm.impl;

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

    public ProgramGraphImpl(){
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
        //addLocation(location); FIXME
        loc0.add(location);
    }

    @Override
    public void addLocation(L l) {
        loc.add(l);
    }

    @Override
    public void addTransition(PGTransition<L, A> t) {
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

    // FIXME: No tests for removing transition / location - clarify.
    @Override
    public void removeLocation(L l) {
        loc.remove(l);
        loc0.remove(l);
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

        if (!name.equals(that.name)) return false;
        if (!init.equals(that.init)) return false;
        if (!loc.equals(that.loc)) return false;
        if (!loc0.equals(that.loc0)) return false;
        return trans.equals(that.trans);
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
