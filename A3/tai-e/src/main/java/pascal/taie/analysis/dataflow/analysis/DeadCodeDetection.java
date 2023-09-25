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
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

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

        // Remove cfg unreachable code, unreachable branch and dead variable
        Stmt entryStmt = cfg.getEntry();
        Queue<Stmt> workList = new LinkedList<>();
        Set<Stmt> visitedSet = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        workList.add(entryStmt);
        visitedSet.add(entryStmt);
        while (!workList.isEmpty()) {
            Stmt visitedStmt = workList.remove();
            // Check if is a condition statement
            // If visited statement is "if" or "switch", check the branch's reachability, or if the statement is a definition statement, check the dead variable
            if (visitedStmt instanceof If ifStmt) {
                ConditionExp condition = ifStmt.getCondition();
                // Check if condition expression is a constant
                CPFact constantsFact = constants.getInFact(ifStmt);
                Value expValue = ConstantPropagation.evaluate(condition, constantsFact);
                if (expValue.isConstant()) {
                    int value = expValue.getConstant();
                    Set<Edge<Stmt>> ifEdges = cfg.getOutEdgesOf(ifStmt);
                    ifEdges.forEach(
                            stmtEdge -> {
                                if ((stmtEdge.getKind() == Edge.Kind.IF_TRUE && value == 1) || (
                                        stmtEdge.getKind() == Edge.Kind.IF_FALSE && value == 0
                                )) {
                                    workList.add(stmtEdge.getTarget());
                                    visitedSet.add(stmtEdge.getTarget());
                                }
                            }
                    );
                    continue;
                }
            } else if (visitedStmt instanceof SwitchStmt switchStmt) {
                Var condition = switchStmt.getVar();
                // Check if condition expression is a constant
                CPFact constantsFact = constants.getInFact(switchStmt);
                Value switchValue = constantsFact.get(condition);
                if (switchValue.isConstant()) {
                    List<Pair<Integer, Stmt>> caseTargets = switchStmt.getCaseTargets();
                    Stmt targetCase = null;
                    for (Pair<Integer, Stmt> target : caseTargets) {
                        if (switchValue.getConstant() == target.first()) {
                            targetCase = target.second();
                            break;
                        }
                    }
                    // If targetCase is not null, add it to the work list. Else, add the default
                    if (targetCase != null) {
                        workList.add(targetCase);
                        visitedSet.add(targetCase);
                    } else {
                        Stmt defaultTarget = switchStmt.getDefaultTarget();
                        if (defaultTarget != null) {
                            workList.add(defaultTarget);
                            visitedSet.add(defaultTarget);
                        }
                    }
                    continue;
                }
            } else if (visitedStmt instanceof AssignStmt<?, ?> assignStmt) {
                if (hasNoSideEffect(assignStmt.getRValue())){
                    SetFact<Var> liveVarSet = liveVars.getOutFact(assignStmt);
                    assignStmt.getDef().ifPresent(
                            lValue -> {
                                if (lValue instanceof Var lVar){
                                    // If not alive, do not visit it.
                                    if(!liveVarSet.contains(lVar)){
                                        visitedSet.remove(visitedStmt);
                                    }
                                }
                            }
                    );
                }
            }
            // Add all the successor to the work list.
            cfg.getSuccsOf(visitedStmt).forEach(
                    stmt -> {
                        if (!visitedSet.contains(stmt)) {
                            workList.add(stmt);
                            visitedSet.add(stmt);
                        }
                    }
            );
        }
        cfg.forEach(
                stmt -> {
                    if (!visitedSet.contains(stmt) && !cfg.isExit(stmt) && !cfg.isEntry(stmt)) {
                        deadCode.add(stmt);
                    }
                }
        );


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
