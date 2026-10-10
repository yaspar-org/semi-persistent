% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% ANCHOR: criterion
% First the number of classes in the term; among terms with the fewest, the number
% of `Add` nodes. A higher priority is more important.
#minimize { 1@2,C : used(C) }.
#minimize { 1@1,N : pick(N), node(N,_,"Add") }.
% ANCHOR_END: criterion
