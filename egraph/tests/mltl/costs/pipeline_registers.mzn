% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
%
% Pipeline register balancing, as costs/pipeline_registers.roto states it, over the
% names of src/extraction/mzn.rs. One unit per operator (a class whose first
% candidate is not a variable or a number), plus one delay register per cycle an
% input waits for the latest input of its operator; the internal nodes of a
% rendered tree are partial results of no latency, ready when their last member is.

function int: latency(int: n) =
    if op[n] = "Add" \/ op[n] = "Neg" then 1
    elseif op[n] = "Mul" then 3
    elseif op[n] = "Div" then 12
    elseif op[n] = "Call1" \/ op[n] = "Call2" \/ op[n] = "Call3" then 20
    else 0 endif;
int: TOP = sum(n in 1..N)(latency(n));

% Arrival: the latency plus the latest operand's arrival.
array[1..C] of var 0..TOP: arr;
constraint forall(n in 1..N)(pick[n] -> arr[cls[n]] = latency(n) + max([0] ++ [arr[k] | k in kids[n]]));

% A block is ready when its last leaf is; the root of n's tree when n starts, its
% latency before its arrival.
array[1..B] of var 0..TOP: ready;
constraint forall(b in 1..B)(ready[b] = max([0] ++ [if bmem[b, p] then arr[leaf[bnode[b], p]] else 0 endif | p in 1..nleaf[bnode[b]]]));
% (Indexed from 0, so the access is total and needs no guard: a partial access makes
% MiniZinc reify a domain test, which Chuffed's FlatZinc parser does not accept.)
array[0..B] of var 0..TOP: ready0 = array1d(0..B, [0] ++ ready);
function var int: start(int: n, var int: g) = if g = 0 then arr[cls[n]] - latency(n) else ready0[g] endif;

% A class waits, under every picked parent, until its innermost block starts: the
% latest of its siblings there. (Taking every leaf of the block, the class included,
% gives the same wait, 0 when the class is itself the latest, with one constraint per
% leaf instead of one per pair of siblings.)
array[1..C] of var 0..TOP: wait;
constraint forall(n in 1..N, p in 1..nleaf[n])(
    pick[n] -> wait[leaf[n, p]] >= start(n, parent_leaf[n, p]) - arr[leaf[n, p]]);

% A partial result waits until its parent block starts.
array[1..B] of var 0..TOP: iwait;
constraint forall(b in 1..B)(inner[b] -> iwait[b] >= start(bnode[b], parent_blk[b]) - ready[b]);

var int: cost = sum(c in 1..C)(bool2int(used[c] /\ op[first[c]] != "Var" /\ op[first[c]] != "Num"))
    + sum(c in 1..C)(wait[c]) + sum(b in 1..B)(iwait[b]);
solve minimize cost;
