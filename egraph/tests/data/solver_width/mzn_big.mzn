% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% Each value fits 64 bits; the objective 2^62 * 3 does not.
var 0..1: x;
var 0..1: y;
constraint x + y >= 1;
solve minimize 4611686018427387904 * 3 * x + 5 * y;
