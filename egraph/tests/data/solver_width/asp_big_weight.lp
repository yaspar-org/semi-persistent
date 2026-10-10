% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% Choose a or b; a costs 3000000000 (past 2^31 - 1), b costs 5. The optimum is b, cost 5.
{ a ; b }.
:- not a, not b.
#minimize { 3000000000,a : a ; 5,b : b }.
