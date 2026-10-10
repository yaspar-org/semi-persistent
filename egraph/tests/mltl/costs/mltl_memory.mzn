% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
%
% R2U2's minimum monitor memory, as costs/mltl_memory.roto states it, over the
% names of src/extraction/mzn.rs. Per class, the queue an early producer needs
% while its latest sibling finishes, max(max sibling wpd - own bpd, 0) + 1, and the
% same for every internal node of a rendered tree, plus the specification's queue.
% A class whose first candidate is a Boolean constant occupies none.

test bounded(int: n) = (op[n] = "Global" \/ op[n] = "Future" \/ op[n] = "Until" \/ op[n] = "Release") /\ nint[n] >= 2;
function int: lb(int: n) = if bounded(n) then max(ints[n, 1], 0) else 0 endif;
function int: ub(int: n) = if bounded(n) then max(ints[n, 2], 0) else 0 endif;
int: TOP = sum(n in 1..N)(ub(n) + lb(n));

% Worst- and best-case propagation delays over the chosen term.
array[1..C] of var 0..TOP: wpd;
array[1..C] of var 0..TOP: bpd;
constraint forall(n in 1..N)(pick[n] -> wpd[cls[n]] = ub(n) + max([0] ++ [wpd[k] | k in kids[n]]));
constraint forall(n in 1..N)(pick[n] -> bpd[cls[n]] = lb(n) + if card(kids[n]) = 0 then 0 else min([bpd[k] | k in kids[n]]) endif);

predicate counted(int: c) = used[c] /\ op[first[c]] != "Bool";
predicate sibling(int: n, int: p, int: q) =
    parent_leaf[n, p] = 0 \/ exists(b in 1..B where bnode[b] = n)(parent_leaf[n, p] = b /\ bmem[b, q]);

array[1..C] of var 0..TOP: queue;
constraint forall(n in 1..N, p, q in 1..nleaf[n] where p != q)(
    (pick[n] /\ sibling(n, p, q) /\ op[first[leaf[n, p]]] != "Bool") -> queue[leaf[n, p]] >= wpd[leaf[n, q]] - bpd[leaf[n, p]]);

% An internal node's queue: its latest outside sibling less its earliest member.
array[1..B] of var 0..TOP: own;
constraint forall(b in 1..B)(own[b] = min([TOP] ++ [if bmem[b, p] then bpd[leaf[bnode[b], p]] else TOP endif | p in 1..nleaf[bnode[b]]]));
array[1..B] of var 0..TOP: iqueue;
constraint forall(b in 1..B, q in 1..nleaf[bnode[b]])(
    (inner[b] /\ not bmem[b, q] /\ (parent_blk[b] = 0 \/ exists(b2 in 1..B where bnode[b2] = bnode[b])(parent_blk[b] = b2 /\ bmem[b2, q])))
    -> iqueue[b] >= wpd[leaf[bnode[b], q]] - own[b]);

var int: cost = 1 + sum(c in 1..C)(bool2int(counted(c))) + sum(c in 1..C)(queue[c])
    + sum(b in 1..B)(bool2int(inner[b])) + sum(b in 1..B)(iqueue[b]);
solve minimize cost;
