% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
%
% History a past-time monitor keeps, as costs/monitor_history.roto states it, over
% the predicates of src/extraction/lp.rs: per used class, the widest window any
% picked parent needs of it (`Formerly(W, phi)` needs phi's history over W,
% `Since(W, A, B)` B's), plus one unit per used class.

window(N,K,W) :- node(N,_,"Formerly"), int(N,0,W), operand(N,K), W > 0.
window(N,K,W) :- node(N,_,"Since"), int(N,0,W), kid(N,1,K), kid(N,_,_), W > 0.
widest(C,W) :- used(C), W = #max { V,N : pick(N), window(N,C,V) ; 0,none }.

#minimize { W,hist,C : widest(C,W) ; 1,eval,C : used(C) }.
