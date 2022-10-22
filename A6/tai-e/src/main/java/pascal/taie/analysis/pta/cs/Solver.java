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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)){
            for (var stmt : csMethod.getMethod().getIR().getStmts()){
                stmt.accept(new StmtProcessor(csMethod));
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt){
            var Ptr = csManager.getCSVar(csMethod.getContext(), stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            CSObj csObj = csManager.getCSObj(contextSelector.selectHeapContext(csMethod,obj),
                    obj);
            PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
            workList.addEntry(Ptr, pointsToSet);
            return StmtVisitor.super.visit(stmt); // gen by IDEA, NULL in manual.
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer source = csManager.getCSVar(csMethod.getContext(), stmt.getRValue());
            Pointer target = csManager.getCSVar(csMethod.getContext(), stmt.getLValue());
            addPFGEdge(source, target);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()){
                return null;
            }
            Pointer target = csManager.getCSVar(csMethod.getContext(), stmt.getLValue());
            Pointer source = csManager.getStaticField(stmt.getFieldRef().resolve());
            addPFGEdge(source, target);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()){
                return null;
            }
            Pointer source = csManager.getCSVar(csMethod.getContext(), stmt.getRValue());
            Pointer target = csManager.getStaticField(stmt.getFieldRef().resolve());
            addPFGEdge(source, target);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()){
                return null;
            }
            JMethod method = resolveCallee(null, stmt);
            var callSite = csManager.getCSCallSite(context, stmt);
            var context = contextSelector.selectContext(callSite, method);
            var csMethod = csManager.getCSMethod(context, method);
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, callSite, csMethod))){
                addReachable(csMethod);
                passArgs(null, stmt, context, callSite);
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    private void passArgs(CSObj recv, Invoke stmt, Context context, CSCallSite csCallSite){
        JMethod jMethod = resolveCallee(recv, stmt);
        Context cTarget = contextSelector.selectContext(csCallSite, recv, jMethod);
        for (int i = 0; i < jMethod.getParamCount(); i++) {
            Pointer source = csManager.getCSVar(context, stmt.getInvokeExp().getArg(i));
            Pointer target = csManager.getCSVar(cTarget, jMethod.getIR().getParam(i));
            addPFGEdge(source, target);
        }
        if (stmt.getResult() == null)
            return;
        Pointer target = csManager.getCSVar(context, stmt.getResult());
        for (Var ret : jMethod.getIR().getReturnVars()) {
            Pointer source = csManager.getCSVar(cTarget, ret);
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
            if (n instanceof CSVar csVar){
                for (var obj : delta.getObjects()){
                    for (var loadField : csVar.getVar().getLoadFields()){
                        var target = csManager.getCSVar(csVar.getContext(), loadField.getLValue());
                        JField jField = loadField.getFieldRef().resolve();
                        var source = csManager.getInstanceField(obj, jField);
                        addPFGEdge(source, target);
                    }
                    for (var storeField : csVar.getVar().getStoreFields()){
                        var source = csManager.getCSVar(csVar.getContext(),storeField.getRValue());
                        JField jField = storeField.getFieldRef().resolve();
                        var target = csManager.getInstanceField(obj, jField);
                        addPFGEdge(source, target);
                    }
                    for (var loadArray : csVar.getVar().getLoadArrays()){
                        var target = csManager.getCSVar(csVar.getContext(), loadArray.getLValue());
                        var source = csManager.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    }
                    for (var storeArray : csVar.getVar().getStoreArrays()){
                        var source = csManager.getCSVar(csVar.getContext(), storeArray.getRValue());
                        var target = csManager.getArrayIndex(obj);
                        addPFGEdge(source, target);
                    }
                    processCall(csVar, obj);
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
        var delta = PointsToSetFactory.make();
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        if (recv == null){
            return;
        }
        for (Invoke invoke : recv.getVar().getInvokes()){
            var method = resolveCallee(recvObj, invoke);
            var mThis = method.getIR().getThis();
            var csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            var cThis = contextSelector.selectContext(csCallSite, recvObj, method);
            var csMethod = csManager.getCSMethod(cThis, method);
            workList.addEntry(csManager.getCSVar(cThis, mThis), PointsToSetFactory.make(recvObj));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csCallSite, csMethod))){
                addReachable(csMethod);
                passArgs(recvObj, invoke, recv.getContext(), csCallSite);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
