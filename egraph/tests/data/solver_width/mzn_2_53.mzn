% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% x costs 2^53 + 1, y costs 2^53: the optimum is y. A solver over doubles cannot tell them apart.
var 0..1: x;
var 0..1: y;
constraint x + y >= 1;
solve minimize 9007199254740993 * x + 9007199254740992 * y;
