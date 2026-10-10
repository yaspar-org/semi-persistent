% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
%
% R2U2's minimum monitor memory, as egraph/tests/mltl/costs/mltl_memory.roto states it, over the
% predicates of egraph/src/extraction/lp.rs. Per class, the queue an early producer needs
% while its latest sibling finishes, max(max sibling wpd - own bpd, 0) + 1, and the
% same for every internal node of a rendered tree, plus the specification's queue.
% A class whose first candidate is a Boolean constant occupies none.

% ANCHOR: criterion
temporal("Global"). temporal("Future"). temporal("Until"). temporal("Release").
bounded(N) :- node(N,_,Op), temporal(Op), int(N,0,_), int(N,1,_).
lb(N,(V+|V|)/2) :- bounded(N), int(N,0,V).
ub(N,(V+|V|)/2) :- bounded(N), int(N,1,V).
lb(N,0) :- node(N,_,_), not bounded(N).
ub(N,0) :- node(N,_,_), not bounded(N).
has_operand(N) :- operand(N,_).

% Worst- and best-case propagation delays over the chosen term. On an acyclic term
% each is at most the sum of its offsets; the bounds keep grounding finite where the
% e-graph has a cycle, which no term can take.
utop(S) :- S = #sum { V,N : ub(N,V) }.
ltop(S) :- S = #sum { V,N : lb(N,V) }.
wpd(C,O+M) :- pick(N), node(N,C,_), ub(N,O), has_operand(N), M = #max { A,K : operand(N,K), wpd(K,A) }, utop(S), O+M <= S.
wpd(C,O)   :- pick(N), node(N,C,_), ub(N,O), not has_operand(N).
bpd(C,O+M) :- pick(N), node(N,C,_), lb(N,O), has_operand(N), M = #min { A,K : operand(N,K), bpd(K,A) }, ltop(S), O+M <= S.
bpd(C,O)   :- pick(N), node(N,C,_), lb(N,O), not has_operand(N).

counted(C) :- used(C), first(C,N), node(N,_,Op), Op != "Bool".
sibw(C,A) :- pick(N), leaf(N,P,C), parent(N,leaf(P),G), bmem(N,G,Q), Q != P, leaf(N,Q,S), wpd(S,A).
% (The latest sibling is taken first and subtracted after, so the aggregate is not
% grounded once per value of the class's own delay.)
latest(C,X) :- counted(C), X = #max { A : sibw(C,A) }.
queue(C,X-B) :- counted(C), bpd(C,B), latest(C,X), X > B.

own(N,B,M) :- inner(N,B), M = #min { A,Q : bmem(N,B,Q), leaf(N,Q,S), bpd(S,A) }.
blatest(N,B,X) :- inner(N,B), parent(N,B,G), X = #max { A,Q : bmem(N,G,Q), not bmem(N,B,Q), leaf(N,Q,S), wpd(S,A) }.
iqueue(N,B,X-M) :- own(N,B,M), blatest(N,B,X), X > M.

#minimize { 1,spec : #true ; 1,cls,C : counted(C) ; W,queue,C : queue(C,W) ; 1,inner,N,B : inner(N,B) ; W,iqueue,N,B : iqueue(N,B,W) }.
% ANCHOR_END: criterion
