/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import fj.test.Bool;
import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()){
            JMethod work = workList.poll();
            if (!callGraph.addReachableMethod(work)) continue;
            for (Invoke callSite : callGraph.getCallSitesIn(work)){
                var target = resolve(callSite);
                for (var method : target){
                    if (method == null) continue;
                    var edge = new Edge<>(CallGraphs.getCallKind(callSite), callSite, method);
                    callGraph.addEdge(edge);
                    workList.add(method);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> target = new HashSet<>();
        var callSiteMethodRef = callSite.getMethodRef();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC -> {
                target.add(callSiteMethodRef.getDeclaringClass().getDeclaredMethod(callSiteMethodRef.getSubsignature()));
            }
            case SPECIAL -> {
                target.add(dispatch(callSiteMethodRef.getDeclaringClass(), callSiteMethodRef.getSubsignature()));
            }
            case VIRTUAL, INTERFACE -> {
                Set<JClass> subClazz = new HashSet<>();
                Queue<JClass> newClazz = new LinkedList<>();// added in an iterate
                JClass recv = callSiteMethodRef.getDeclaringClass();
                newClazz.add(recv);
                boolean changed = true;
                while (!newClazz.isEmpty()){
                    JClass tmp = newClazz.poll();
                    newClazz.addAll(hierarchy.getDirectSubclassesOf(tmp));
                    newClazz.addAll(hierarchy.getDirectImplementorsOf(tmp));
                    newClazz.addAll(hierarchy.getDirectSubinterfacesOf(tmp));
                    changed = subClazz.addAll(newClazz); // maybe no need?
                }
                subClazz.add(recv);
                for (var subclass : subClazz) {
                    System.out.println("Find subclass of" + subclass.toString());
                    target.add(dispatch(subclass, callSiteMethodRef.getSubsignature()));
                }
            }
        }
        return target;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        var method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract()){
            return jclass.getDeclaredMethod(subsignature);
        }
        if (jclass.getSuperClass() != null){
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        return null;
    }
}
