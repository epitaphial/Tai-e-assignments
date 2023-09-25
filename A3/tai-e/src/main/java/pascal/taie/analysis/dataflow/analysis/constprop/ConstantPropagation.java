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
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

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
        CPFact cpFact = new CPFact();
        // Initialize all the params to NAC.
        cfg.getIR().getParams().forEach(
                param -> {
                    if (canHoldInt(param)){
                        cpFact.update(param, Value.getNAC());
                    }
                }
        );
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((key, value) -> target.update(key, meetValue(value, target.get(key))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isConstant()) {
            if (v2.isConstant()) {
                if (v1.getConstant() == v2.getConstant()) {
                    return v1;
                } else {
                    return Value.getNAC();
                }
            } else if (v2.isUndef()) {
                return v1;
            } else if (v2.isNAC()) {
                return v2;
            } else {
                throw new RuntimeException("Can not be other types!");
            }
        } else if (v1.isUndef()) {
            if (v2.isConstant()) {
                return v2;
            } else if (v2.isUndef()) {
                return v1;
            } else if (v2.isNAC()) {
                return v2;
            } else {
                throw new RuntimeException("Can not be other types!");
            }
        } else if (v1.isNAC()) {
            return v1;
        } else {
            throw new RuntimeException("Can not be other types!");
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact copyIn = in.copy();
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            LValue lValue = definitionStmt.getLValue();
            if (lValue instanceof Var lVar) {
                if (canHoldInt(lVar)) {
                    // Kill the redefined vars
                    copyIn.remove((Var) lValue);
                    // Add the generated vars to the fact.
                    RValue rValue = definitionStmt.getRValue();
                    if (rValue instanceof Var rVar) {
                        copyIn.update(lVar, in.get(rVar));
                    } else if (rValue instanceof IntLiteral rVar) {
                        copyIn.update(lVar, Value.makeConstant(rVar.getValue()));
                    } else if (rValue instanceof BinaryExp rVar) {
                        Value expValue = evaluate(rVar, in);
                        if (expValue != null) {
                            copyIn.update(lVar, expValue);
                        } else {
                            throw new RuntimeException("Expression can not be null!");
                        }
                    } else {
                        // Maybe it is an invoke expression.
                        copyIn.update(lVar,Value.getNAC());
                    }
                }

            }
        }
        if (copyIn.equals(out)) {
            return false;
        } else {
            out.clear();
            copyIn.forEach(out::update);
            return true;
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE, SHORT, INT, CHAR, BOOLEAN -> {
                    return true;
                }
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
        BinaryExp binaryExp = (BinaryExp) exp;
        Value lValue = in.get(binaryExp.getOperand1());
        Value rValue = in.get(binaryExp.getOperand2());
        if (lValue.isNAC() || rValue.isNAC()) {
            // Deal with NAC/0 and NAC mod 0
            if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                ArithmeticExp.Op op = arithmeticExp.getOperator();
                if ((op.equals(ArithmeticExp.Op.DIV) || op.equals(ArithmeticExp.Op.REM)) && rValue.isConstant() && rValue.getConstant() == 0) {
                    return Value.getUndef();
                } else {
                    return Value.getNAC();
                }
            } else {
                return Value.getNAC();
            }
        } else if (lValue.isConstant() && rValue.isConstant()) {
            if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                ArithmeticExp.Op op = arithmeticExp.getOperator();
                switch (op) {
                    case ADD -> {
                        return Value.makeConstant(lValue.getConstant() + rValue.getConstant());
                    }
                    case SUB -> {
                        return Value.makeConstant(lValue.getConstant() - rValue.getConstant());
                    }
                    case MUL -> {
                        return Value.makeConstant(lValue.getConstant() * rValue.getConstant());
                    }
                    case DIV -> {
                        int constRValue = rValue.getConstant();
                        return constRValue == 0 ? Value.getUndef() : Value.makeConstant(lValue.getConstant() / rValue.getConstant());
                    }
                    case REM -> {
                        int constRValue = rValue.getConstant();
                        return constRValue == 0 ? Value.getUndef() : Value.makeConstant(lValue.getConstant() % rValue.getConstant());
                    }
                    default -> throw new RuntimeException("No more kind of operators!");
                }
            } else if (binaryExp instanceof BitwiseExp bitwiseExp) {
                BitwiseExp.Op op = bitwiseExp.getOperator();
                switch (op) {
                    case AND -> {
                        return Value.makeConstant(lValue.getConstant() & rValue.getConstant());
                    }
                    case OR -> {
                        return Value.makeConstant(lValue.getConstant() | rValue.getConstant());
                    }
                    case XOR -> {
                        return Value.makeConstant(lValue.getConstant() ^ rValue.getConstant());
                    }
                    default -> throw new RuntimeException("No more kind of operators!");
                }
            } else if (binaryExp instanceof ConditionExp conditionExp) {
                ConditionExp.Op op = conditionExp.getOperator();
                switch (op) {
                    case EQ -> {
                        return Value.makeConstant(lValue.getConstant() == rValue.getConstant() ? 1 : 0);
                    }
                    case NE -> {
                        return Value.makeConstant(lValue.getConstant() != rValue.getConstant() ? 1 : 0);
                    }
                    case GE -> {
                        return Value.makeConstant(lValue.getConstant() >= rValue.getConstant() ? 1 : 0);
                    }
                    case GT -> {
                        return Value.makeConstant(lValue.getConstant() > rValue.getConstant() ? 1 : 0);
                    }
                    case LE -> {
                        return Value.makeConstant(lValue.getConstant() <= rValue.getConstant() ? 1 : 0);
                    }
                    case LT -> {
                        return Value.makeConstant(lValue.getConstant() < rValue.getConstant() ? 1 : 0);
                    }
                    default -> throw new RuntimeException("No more kind of operators!");
                }
            } else if (binaryExp instanceof ShiftExp shiftExp) {
                ShiftExp.Op op = shiftExp.getOperator();
                switch (op) {
                    case SHL -> {
                        return Value.makeConstant(lValue.getConstant() << rValue.getConstant());
                    }
                    case SHR -> {
                        return Value.makeConstant(lValue.getConstant() >> rValue.getConstant());
                    }
                    case USHR -> {
                        return Value.makeConstant(lValue.getConstant() >>> rValue.getConstant());
                    }
                    default -> throw new RuntimeException("No more kind of operators!");
                }
            } else {
                throw new RuntimeException("No more kind of expressions!");
            }
        } else {
            return Value.getUndef();
        }
    }
}
