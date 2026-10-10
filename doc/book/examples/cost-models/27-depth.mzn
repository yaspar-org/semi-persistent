% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% ANCHOR: criterion
% The depth of the deepest leaf of any picked node, a leaf directly under its node
% at depth 1.
var 0..MAXL: deepest;
constraint forall(n in 1..N, p in 1..nleaf[n])(pick[n] -> deepest >= depth[n, p]);
solve minimize deepest;
% ANCHOR_END: criterion
