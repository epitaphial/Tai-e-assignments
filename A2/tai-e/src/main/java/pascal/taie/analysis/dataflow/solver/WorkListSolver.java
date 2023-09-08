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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.*;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        List<Node> workList = new ArrayList<>();
        cfg.forEach(
                workList::add
        );
        while (!workList.isEmpty()) {
            Node workNode = workList.get(0);
            Fact targetFact = result.getInFact(workNode);
            // Traverse the predecessor of current node and do meet.
            cfg.getPredsOf(workNode).forEach(
                    node -> analysis.meetInto(result.getOutFact(node), targetFact)
            );

            // Run transfer function.
            if (analysis.transferNode(workNode, targetFact, result.getOutFact(workNode))) {
                cfg.getSuccsOf(workNode).forEach(
                        node -> {
                            if (!workList.contains(node)) {
                                workList.add(node);
                            }
                        }
                );
            } else {
                workList.remove(workNode);
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
