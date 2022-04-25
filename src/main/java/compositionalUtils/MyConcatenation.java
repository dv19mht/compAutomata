/*
 * (C) Copyright 2001 Arnaud Bailly (arnaud.oqube@gmail.com),
 *     Yves Roos (yroos@lifl.fr) and others.
 *
 * Licensed under the Apache License, Version 2.0 (the License);
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an AS IS BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package compositionalUtils;

import rationals.Automaton;
import rationals.Builder;
import rationals.NoSuchStateException;
import rationals.State;
import rationals.Transition;
import rationals.transformations.BinaryTransformation;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Compute the concatenation of two automata.
 * <ul>
 * <li>C = A . B</li>
 * <li>S(C) = S(A) U S(B)</li>
 * <li>S0(C) =
 * <ul>
 * <li>S0(A), if not A contains epsilon,</li>
 * <li>S0(A) U SO(B), otherwise</li>
 * </ul>
 * </li>
 * <li>T(C) =
 * <ul>
 * <li>T(B), if not B contains epsilon,</li>
 * <li>T(A) U T(B), otherwise</li>
 * </ul>
 * </li>
 * <li>D(C) = D(A) U D(B) U { (s1,a,s2) | (s,a,s2) in D(B), s in S0(B),s1 in
 * T(A) } - {(s,a,s2) in D(B), s in S0(B) }</li>
 * </ul>
 *
 * @version $Id: Concatenation.java 2 2006-08-24 14:41:48Z oqube $
 */
public class MyConcatenation<L, Tr extends Transition<L>, T extends Builder<L, Tr, T>> implements BinaryTransformation<L, Tr, T> {

    public Automaton<L, Tr, T> transform(Automaton<L, Tr, T> a, Automaton<L, Tr, T> b) {
        Automaton<L, Tr, T> ap = a.clone();
        Automaton<L, Tr, T> bp = b.clone();

        Automaton<L, Tr, T> c = new Automaton<>();
        Map<State, State> map = new HashMap<>();
        Map<State, State> reversedMap = new HashMap<>();

        /* add all states from ap */
        Iterator<State> i1 = ap.states().iterator();
        while (i1.hasNext()) {
            State e = i1.next();
            State n = c.addState(e.isInitial(), e.isTerminal());
            map.put(e, n);
            reversedMap.put(n, e);
        }

        /* add states from bp */
        Iterator<State> i2 = bp.states().iterator();
        while (i2.hasNext()) {
            State e = i2.next();
            State n = c.addState(e.isInitial(), e.isTerminal());
            map.put(e, n);
            reversedMap.put(n, e);
        }

        /* create junction state */
        Iterator<Transition<L>> i3 = ap.delta().iterator();
        while (i3.hasNext()) {
            Transition<L> t = i3.next();
            try {
                c.addTransition(new Transition<>(map.get(t.start()), t.label(), map.get(t.end())));
                if (t.end().isTerminal()) {
                    /* add epsilon transitions to initial states in b */
                    Set<State> bpInitials = bp.initials();
                    for (State s : bpInitials) {
                        c.addTransition(new Transition<>(map.get(t.end()), null, map.get(s)));
                        map.get(s).setInitial(false);
                    }
                }
            } catch (NoSuchStateException x) {
                throw new IllegalArgumentException("No such state");
            }
        }

        Iterator<Transition<L>> i4 = bp.delta().iterator();
        while (i4.hasNext()) {
            Transition<L> t = i4.next();
            try {
                c.addTransition(new Transition<>(map.get(t.start()), t.label(), map.get(t.end())));
                if (t.start().isInitial()) {
                    /* add epsilon transitions to terminal states in a */
                    Set<State> apTerminals = ap.terminals();
                    for (State s : apTerminals) {
                        c.addTransition(new Transition<>(map.get(s), null, map.get(t.start())));
                        map.get(s).setTerminal(false);
                    }
                }
            } catch (NoSuchStateException x) {
                throw new IllegalArgumentException("No such state");
            }
        }

        Set<State> cInitials = c.initials();
        for (State s : cInitials) {
            State possAInitial = reversedMap.get(s);
            if (bp.initials().contains(possAInitial) && !(ap.initials().contains(possAInitial))) {
                s.setInitial(false);
            }

            if (ap.terminals().contains(possAInitial) && !(bp.terminals().contains(possAInitial))) {
                s.setTerminal(false);
            }
        }

        return c;
    }
}