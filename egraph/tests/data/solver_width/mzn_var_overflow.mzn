% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% No constant overflows; the objective's bound, 4 * 2^62 = 2^64, does.
var 0..4611686018427387904: x;
constraint x >= 1;
solve minimize 4 * x;
