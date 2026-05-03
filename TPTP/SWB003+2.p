%------------------------------------------------------------------------------
% File     : SWB003+2 : TPTP v9.2.1. Released v5.2.0.
% Domain   : Semantic Web
% Problem  : Blank Nodes for Literals
% Version  : [Sch11] axioms : Reduced > Incomplete.
% English  :

% Refs     : [Sch11] Schneider, M. (2011), Email to G. Sutcliffe
% Source   : [Sch11]
% Names    : 003_Blank_Nodes_for_Literals [Sch11]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.04 v5.2.0
% Syntax   : Number of formulae    :    2 (   2 unt;   0 def)
%            Number of atoms       :    2 (   0 equ)
%            Maximal formula atoms :    1 (   1 avg)
%            Number of connectives :    0 (   0   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    2 (   2 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    4 (   4 usr;   3 con; 0-1 aty)
%            Number of variables   :    1 (   0   !;   1   ?)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%------------------------------------------------------------------------------
fof(testcase_conclusion_fullish_003_Blank_Nodes_for_Literals,conjecture,
    ?[BNODE_x] : iext(uri_ex_p,uri_ex_s,BNODE_x) ).

fof(testcase_premise_fullish_003_Blank_Nodes_for_Literals,axiom,
    iext(uri_ex_p,uri_ex_s,literal_plain(dat_str_foo)) ).

%------------------------------------------------------------------------------
