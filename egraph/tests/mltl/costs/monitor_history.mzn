% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
%
% History a past-time monitor keeps, as costs/monitor_history.roto states it, over
% the names of src/extraction/mzn.rs: per used class, the widest window any picked
% parent needs of it (`Formerly(W, phi)` needs phi's history over W,
% `Since(W, A, B)` B's), plus one unit per used class.

function int: window(int: n, int: k) =
    if nint[n] >= 1 /\ ints[n, 1] > 0 /\ (op[n] = "Formerly" \/ (op[n] = "Since" /\ nkid[n] >= 2 /\ kid[n, 2] = k))
    then ints[n, 1] else 0 endif;
int: TOP = max([0] ++ [ints[n, 1] | n in 1..N where nint[n] >= 1]);
array[1..C] of var 0..TOP: widest;
constraint forall(n in 1..N, k in kids[n] where window(n, k) > 0)(pick[n] -> widest[k] >= window(n, k));

var int: cost = sum(c in 1..C)(widest[c]) + sum(c in 1..C)(bool2int(used[c]));
solve minimize cost;
