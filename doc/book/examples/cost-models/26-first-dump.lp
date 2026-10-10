% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% The facts Semper writes for 26-first.egg at the selection rung, as kept by
% EXTRACT_API_KEEP_LP. The rules that follow them in the program are not shown.
% ANCHOR: facts
% The e-graph.
root(3).
class(0).
first(0,3).
node(3,0,"V").
kind(3,plain).
str(3,0,"a").
class(1).
first(1,0).
node(0,1,"F").
kind(0,plain).
kid(0,0,0).
operand(0,0). mult(0,0,1).
leaf(0,0,0).
class(2).
first(2,4).
node(4,2,"F").
kind(4,plain).
kid(4,0,1).
operand(4,1). mult(4,1,1).
leaf(4,0,1).
class(3).
first(3,1).
node(1,3,"Add").
kind(1,plain).
kid(1,0,2).
kid(1,1,2).
operand(1,2). mult(1,2,2).
leaf(1,0,2).
node(2,3,"Twice").
kind(2,plain).
kid(2,0,2).
operand(2,2). mult(2,2,1).
leaf(2,0,2).
% ANCHOR_END: facts
