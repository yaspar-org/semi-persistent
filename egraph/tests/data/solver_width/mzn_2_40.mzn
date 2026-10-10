% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% 2^40 fits 64 bits and not 32; the optimum is y, objective 5.
var 0..1: x;
var 0..1: y;
constraint x + y >= 1;
solve minimize 1099511627776 * x + 5 * y;
