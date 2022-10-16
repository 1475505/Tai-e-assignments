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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.lang.reflect.Array;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)){
            for (Stmt stmt : method.getIR().getStmts()){
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt){
            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            PointsToSet pointsToSet = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(varPtr, pointsToSet);
            return StmtVisitor.super.visit(stmt); // gen by IDEA, NULL in manual.
        }

        @Override
        public Void visit(Copy stmt) {
            VarPtr source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            VarPtr target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            addPFGEdge(source, target);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()){
                return null;
            }
            VarPtr target = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var source = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
            addPFGEdge(source, target);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()){
                return null;
            }
            VarPtr source = pointerFlowGraph.getVarPtr(stmt.getRValue());
            var target = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
            addPFGEdge(source, target);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()){
                return null;
            }
            var method = resolveCallee(null, stmt);
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method))){
                addReachable(method);
                passArgs(method, stmt);
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    private void passArgs(JMethod method, Invoke stmt){
        for (int i = 0; i < method.getParamCount(); i++) {
            VarPtr source = pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i));
            VarPtr target = pointerFlowGraph.getVarPtr(method.getIR().getParam(i));
            addPFGEdge(source, target);
        }
        if (stmt.getResult() == null)
            return;
        VarPtr target = pointerFlowGraph.getVarPtr(stmt.getResult());
        for (Var ret : method.getIR().getReturnVars()) {
            VarPtr source = pointerFlowGraph.getVarPtr(ret);
            addPFGEdge(source, target);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)){
            if (!source.getPointsToSet().isEmpty()){
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()){
            var entry = workList.pollEntry();
            var n = entry.pointer();
            var pts = entry.pointsToSet();
            var delta = propagate(n, pts);
            if (n instanceof VarPtr varPtr){
                for (var obj : delta.getObjects()){
                    for (var loadField : varPtr.getVar().getLoadFields()){
                        var target = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        JField jField = loadField.getFieldRef().resolve();
                        var source = pointerFlowGraph.getInstanceField(obj, jField);
                        addPFGEdge(source, target);
                    }
                    for (var storeField : varPtr.getVar().getStoreFields()){
                        var source = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        JField jField = storeField.getFieldRef().resolve();
                        var target = pointerFlowGraph.getInstanceField(obj, jField);
                        addPFGEdge(source, target);
                    }
                    for (var loadArray : varPtr.getVar().getLoadArrays()){
                        var target = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        var source = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    }
                    for (var storeArray : varPtr.getVar().getStoreArrays()){
                        var source = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        var target = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    }
                    processCall(varPtr.getVar(), obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var delta = new PointsToSet();
        if (pointsToSet.isEmpty()){
            return delta;
        }
        var pt_n = pointer.getPointsToSet();
        for (var pt : pointsToSet){
            if (pt_n.contains(pt))
                continue;
            pointer.getPointsToSet().addObject(pt);
            delta.addObject(pt);
        }
        for (var pt : pointerFlowGraph.getSuccsOf(pointer)){
            workList.addEntry(pt, delta);
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke callSite : var.getInvokes()){
            var method = resolveCallee(recv, callSite);
            var mThis = method.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(mThis), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, method))){
                addReachable(method);
                passArgs(method, callSite);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
