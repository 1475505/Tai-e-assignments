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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.MapFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact cpFact = new CPFact();
        for (Var param : cfg.getIR().getParams() ){
            if (canHoldInt(param)){
                cpFact.update(param, Value.getNAC());
                // Actually, absence means "UNDEF", i.e. TOP.
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        target.forEach((Var var, Value value) -> {
            target.update(var, meetValue(fact.get(var), value));
        });
        fact.forEach((Var var, Value value) -> {
            target.update(var, meetValue(target.get(var), value));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }
        if (v1.isUndef())   return v2;
        if (v2.isUndef())   return v1;
        if (v1.getConstant() == v2.getConstant()){
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        var gen = stmt.getDef();
        CPFact old_out = out.copy();
        out.copyFrom(in);
        if (gen.isPresent() && gen.get() instanceof Var) {
            if (canHoldInt((Var) gen.get()) && ((DefinitionStmt<?, ?>) stmt).getRValue() != null) {
                out.update((Var) gen.get(), evaluate(((DefinitionStmt<?, ?>) stmt).getRValue(), in));
                System.out.println((((DefinitionStmt<?, ?>) stmt).getRValue()).toString());
            } else {
                out.update((Var) gen.get(), Value.getNAC());
            }
            System.out.println(stmt.getLineNumber() + " | transferred (old_out:" + old_out.toString() + ")"+ stmt.toString() + " from" + in.toString() + "->" + out.toString());
        }
        return out.equals(old_out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var){
            if (canHoldInt((Var) exp)) {
                System.out.println("Evaluate Var " + exp.toString() + "==" + in.get((Var) exp).toString());
                return in.get((Var) exp);
            } else {
                return Value.getNAC();
            }
        } else if (exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral)exp).getValue());
        } else if (exp instanceof BinaryExp){
            Value op1 = evaluate(((BinaryExp) exp).getOperand1(), in);
            Value op2 = evaluate(((BinaryExp) exp).getOperand2(), in);
            if ( op1.isNAC() || op2.isNAC()){
                return Value.getNAC();
            }
            if ( !op1.isConstant() || !op2.isConstant()){
                return Value.getUndef();
            }
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();
            if (op instanceof ArithmeticExp.Op) {
                switch ((ArithmeticExp.Op)op) {
                    case ADD -> {
                        return Value.makeConstant(op1.getConstant() + op2.getConstant());
                    }
                    case SUB -> {
                        return Value.makeConstant(op1.getConstant() - op2.getConstant());
                    }
                    case MUL -> {
                        return Value.makeConstant(op1.getConstant() * op2.getConstant());
                    }
                    case DIV -> {
                        if (op2.getConstant() == 0) {
                            return Value.getUndef();
                        }
                        return Value.makeConstant(op1.getConstant() / op2.getConstant());
                    }
                    case REM -> {
                        if (op2.getConstant() == 0) {
                            return Value.getUndef();
                        }
                        return Value.makeConstant(op1.getConstant() % op2.getConstant());
                    }
                }
            }
            if (op instanceof ConditionExp.Op){
                switch ((ConditionExp.Op)op){
                    case EQ -> {
                        return Value.makeConstant(op1.getConstant() == op2.getConstant()? 1 : 0);
                    }
                    case GE -> {
                        return Value.makeConstant(op1.getConstant() >= op2.getConstant()? 1 : 0);
                    }
                    case GT -> {
                        return Value.makeConstant(op1.getConstant() > op2.getConstant()? 1 : 0);
                    }
                    case LE -> {
                        return Value.makeConstant(op1.getConstant() <= op2.getConstant()? 1 : 0);
                    }
                    case LT -> {
                        return Value.makeConstant(op1.getConstant() < op2.getConstant()? 1 : 0);
                    }
                    case NE -> {
                        return Value.makeConstant(op1.getConstant() != op2.getConstant()? 1 : 0);
                    }
                }
            }
            if (op instanceof ShiftExp.Op){
                switch ((ShiftExp.Op)op){
                    case SHL -> {
                        return Value.makeConstant(op1.getConstant() << op2.getConstant());
                    }
                    case SHR -> {
                        return Value.makeConstant(op1.getConstant() >> op2.getConstant());
                    }
                    case USHR -> {
                        return Value.makeConstant(op1.getConstant() >>> op2.getConstant());
                    }
                }
            }
            if (op instanceof BitwiseExp.Op) {
                // maybe no need to process it? NO!!! logic rather than bitwise.
                switch ((BitwiseExp.Op)op){
                    case OR -> {
                        return Value.makeConstant(op1.getConstant() | op2.getConstant());
                    }
                    case AND -> {
                        return Value.makeConstant(op1.getConstant() & op2.getConstant());
                    }
                    case XOR -> {
                        return Value.makeConstant(op1.getConstant() ^ op2.getConstant());
                    }
                }
            }
            return Value.getUndef();
        }
        /*
        f(y,z) =
            val(y) op val(z) // if val(y) and val(z) are constants
            NAC // if val(y) or val(z) is NAC
            UNDEF // otherwise
         对于其它情况，该方法会像我们在第 2.1 节提到的那样返回 NAC。
         */
        return Value.getNAC();
    }
}
