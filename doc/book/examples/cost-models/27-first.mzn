% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% ANCHOR: criterion
% Every picked node is paid once: `Twice` 3, every other operator 1.
array[1..N] of int: price = [if op[n] = "Twice" then 3 else 1 endif | n in 1..N];
var int: cost = sum(n in 1..N)(price[n] * bool2int(pick[n]));
solve minimize cost;
% ANCHOR_END: criterion
