% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% ANCHOR: criterion
% The depth of the deepest leaf of any picked node, a leaf directly under its node
% at depth 1.
deepest(D) :- D = #max { X,N,P : pick(N), depth(N,P,X) ; 0 }.
#minimize { D : deepest(D) }.
% ANCHOR_END: criterion
