% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% The data Semper writes for 27-first.egg at the selection rung, as kept by
% EXTRACT_API_KEEP_MZN. The variables and constraints that follow are not shown.
% ANCHOR: data
% The e-graph.
int: C = 4;
int: N = 5;
int: B = 0;
int: MAXK = 2;
int: MAXL = 1;
int: MAXJ = 1;
int: ROOT = 4;
int: PLAIN = 0; int: COMM = 1; int: SEQ = 2; int: SEQ_LEFT = 3; int: SEQ_RIGHT = 4; int: MSET = 5; int: SET = 6;
array[1..C] of int: class_id = [0, 1, 2, 3];
array[1..N] of int: node_id = [3, 0, 4, 1, 2];
array[1..N] of 1..C: cls = [1, 2, 3, 4, 4];
array[1..N] of string: op = ["V", "F", "F", "Add", "Twice"];
array[1..N] of int: kind = [0, 0, 0, 0, 0];
array[1..N] of set of 1..C: kids = [{}, {1}, {2}, {3}, {3}];
array[1..N] of int: nkid = [0, 1, 1, 2, 1];
array[1..N, 1..MAXK] of 0..C: kid = [| 0, 0 | 1, 0 | 2, 0 | 3, 3 | 3, 0 |];
array[1..N, 1..MAXK] of int: kmult = [| 0, 0 | 1, 0 | 1, 0 | 1, 1 | 1, 0 |];
function int: mult(int: n, int: k) = sum(i in 1..nkid[n])(if kid[n, i] = k then kmult[n, i] else 0 endif);
array[1..N] of int: nint = [0, 0, 0, 0, 0];
array[1..N, 1..MAXJ] of int: ints = [| 0 | 0 | 0 | 0 | 0 |];
array[1..C] of 1..N: first = [1, 2, 3, 4];
array[1..N] of int: nleaf = [0, 1, 1, 1, 1];
array[1..N, 1..MAXL] of 0..C: leaf = [| 0 | 1 | 2 | 3 | 3 |];
% 0 no tree, 1 chains, 2 trees, 3 binary trees, 4 ordered trees, 5 a fold.
array[1..N] of int: family = [0, 0, 0, 0, 0];
array[1..B] of 1..N: bnode = [];
array[1..B] of bool: interval = [];
array[1..B] of int: blo = [];
array[1..B] of int: bhi = [];
% ANCHOR_END: data
