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

package pascal.taie.analysis.dataflow.analysis;

import fj.test.Bool;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode.
        Set<Stmt> liveStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Queue<Stmt> queue = new LinkedList<>();
        queue.offer(cfg.getEntry());
        while (!queue.isEmpty()){ //BFS
            Stmt stmt = queue.poll();
            System.out.println("Start process: " + stmt);
            // 1. 如果不存在从程序入口到达某一段代码的控制流路径，那么这一段代码就是控制流不可达的。
            // 这样的代码可以很简单地利用所在方法的控制流图（CFG，即 control-flow graph）检测出来。
            // 我们只需要从方法入口开始，遍历 CFG 并标记可达语句。
            // 当遍历结束时，那些没有被标记的语句就是控制流不可达的。
            if (deadCode.contains(stmt))    continue;
            liveStmt.add(stmt);
            for (var edge : cfg.getOutEdgesOf(stmt)){
                if (liveStmt.contains(edge.getTarget()) || deadCode.contains(edge.getTarget()))
                    continue;
                queue.offer(edge.getTarget());
            }

            //2. 分支不可达代码.
            //为了检测分支不可达代码，我们需要预先对被检测代码应用常量传播分析，通过它来告诉我们条件值是否为常量，(constants)
            //然后在遍历 CFG 时，我们不进入相应的不可达分支。
            //(1) 对于一个 if 语句，如果它的条件值（通过常量传播得知）是一个常数，那么它两个分支中的其中一个分支必然不会被走到。
            //    这样的分支被称为不可达分支。
            //(2) 对于一个 switch 语句，如果它的条件值是个常数，那么不符合条件值的 case 分支**可能**(fallthrough)是不可达的。
            if (stmt instanceof If ifStmt){
                var cond = ifStmt.getCondition();
                var condVal = ConstantPropagation.evaluate(cond, constants.getInFact(stmt));
                if (condVal.isConstant()){
                    for (var edge : cfg.getOutEdgesOf(stmt)){
                        int ifVal = (edge.getKind() == Edge.Kind.IF_FALSE)? 0: 1;
                        if (ifVal != condVal.getConstant()){
                            System.out.println("Got deadcode: if " + ifVal + "|" + stmt);
                            deadCode.add(edge.getTarget());
                        }
                    }
                }
            }
            if (stmt instanceof SwitchStmt switchStmt){
                var switchVal = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(stmt));
                if (switchVal.isConstant()){
                    var caseNo = switchStmt.getCaseValues().indexOf(switchVal.getConstant());
                    int casesCnt = switchStmt.getCaseValues().size();
                    if (caseNo == -1){
                        for (var branch : switchStmt.getCaseTargets()){
                            deadCode.add(branch.second());
                        }
                    } else {
                        queue.remove(switchStmt.getDefaultTarget());
                        for (int i = 0; i < casesCnt; i++){
                            if (i != caseNo){
                                queue.remove(switchStmt.getTarget(i));
                            }
                        }

                    }
                }
            }
            // 3. 无用赋值
            // 一个局部变量在一条语句中被赋值，但再也没有被该语句后面的语句读取，这样的变量和语句分别被称为无用变量（dead variable，与活跃变量 live variable 相对）和无用赋值。
            // 检测方式：为了检测无用赋值，我们需要预先对被检测代码施用活跃变量分析。对于一个赋值语句，如果它等号左侧的变量（LHS 变量）是一个无用变量（换句话说，not live），且右边的表达式 expr 没有副作用，那么我们可以把它标记为一个无用赋值。
            if (stmt instanceof AssignStmt<?,?> assignStmt) {
                var lValue = assignStmt.getLValue();
                var rValue = assignStmt.getRValue();
                if (DeadCodeDetection.hasNoSideEffect(rValue) && lValue instanceof Var def && !liveVars.getResult(stmt).contains(def)){
                    deadCode.add(stmt);
                }
            }
        }
        // Other kinds of Stmt, like: foo()
        for (var stmt : cfg) {
            if (cfg.isEntry(stmt) || cfg.isExit(stmt))
                continue;
            if (!liveStmt.contains(stmt)) {
                deadCode.add(stmt);
                System.out.println("Got deadcode not in CFG " + "|" + stmt);
            }
        }
        return deadCode;
    }


    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
