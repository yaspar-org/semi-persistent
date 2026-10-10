% Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
% SPDX-License-Identifier: Apache-2.0
% Both forced; each weight fits 32 bits, the sum 4000000000 does not.
a. b.
#minimize { 2000000000,a : a ; 2000000000,b : b }.
