% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
%
% Pipeline register balancing, as costs/pipeline_registers.roto states it, over the
% predicates of src/extraction/lp.rs. One unit per operator (a class whose first
% candidate is not a variable or a number), plus one delay register per cycle an
% input waits for the latest input of its operator; the internal nodes of a
% rendered tree are partial results of no latency, ready when their last member is.

latency("Add",1). latency("Neg",1). latency("Mul",3). latency("Div",12).
latency("Call1",20). latency("Call2",20). latency("Call3",20).
timed(N) :- node(N,_,Op), latency(Op,_).
lat(N,L) :- node(N,_,Op), latency(Op,L).
lat(N,0) :- node(N,_,_), not timed(N).
has_operand(N) :- operand(N,_).

% Arrival: the latency plus the latest operand's arrival. On an acyclic term it is at
% most the sum of all latencies; the bound keeps grounding finite where the e-graph
% has a cycle, which no term can take.
top(S) :- S = #sum { L,N : lat(N,L) }.
arr(C,L+M) :- pick(N), node(N,C,_), lat(N,L), has_operand(N), M = #max { A,K : operand(N,K), arr(K,A) }, top(S), L+M <= S.
arr(C,L)   :- pick(N), node(N,C,_), lat(N,L), not has_operand(N).

% A class waits for the latest sibling in its innermost block, under every parent.
% (The latest sibling is taken first and subtracted after: an aggregate over the
% siblings inside a rule that also binds the class's own arrival would be grounded
% once per value of it.)
sibarr(C,A) :- pick(N), leaf(N,P,C), parent(N,leaf(P),G), bmem(N,G,Q), Q != P, leaf(N,Q,S), arr(S,A).
latest(C,X) :- used(C), X = #max { A : sibarr(C,A) }.
wait(C,X-A0) :- arr(C,A0), latest(C,X), X > A0.

% A partial result waits for the latest sibling of its block.
ready(N,B,M) :- inner(N,B), M = #max { A,Q : bmem(N,B,Q), leaf(N,Q,S), arr(S,A) }.
blatest(N,B,X) :- inner(N,B), parent(N,B,G), X = #max { A,Q : bmem(N,G,Q), not bmem(N,B,Q), leaf(N,Q,S), arr(S,A) }.
iwait(N,B,X-M) :- ready(N,B,M), blatest(N,B,X), X > M.

operator(C) :- used(C), first(C,N), node(N,_,Op), Op != "Var", Op != "Num".

#minimize { 1,op,C : operator(C) ; W,wait,C : wait(C,W) ; W,inner,N,B : iwait(N,B,W) }.
