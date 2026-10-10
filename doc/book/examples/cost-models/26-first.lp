% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% ANCHOR: criterion
% Every picked node is paid once: `Twice` 3, every other operator 1.
price(N,3) :- node(N,_,"Twice").
price(N,1) :- node(N,_,Op), Op != "Twice".
#minimize { P,N : pick(N), price(N,P) }.
% ANCHOR_END: criterion
