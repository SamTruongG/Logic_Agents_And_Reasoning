%------------------------------------------------------------------------------
% File     : SWB002+2 : TPTP v9.2.1. Released v5.2.0.
% Domain   : Semantic Web
% Problem  : Existential Blank Nodes
% Version  : [Sch11] axioms : Reduced > Incomplete.
% English  :

% Refs     : [Sch11] Schneider, M. (2011), Email to G. Sutcliffe
% Source   : [Sch11]
% Names    : 002_Existential_Blank_Nodes [Sch11]

% Status   : Theorem
% Rating   : 0.00 v5.4.0, 0.11 v5.3.0, 0.09 v5.2.0
% Syntax   : Number of formulae    :    2 (   0 unt;   0 def)
%            Number of atoms       :    4 (   0 equ)
%            Maximal formula atoms :    2 (   2 avg)
%            Number of connectives :    2 (   0   ~;   0   |;   2   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   4 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    3 (   3 usr;   3 con; 0-0 aty)
%            Number of variables   :    3 (   0   !;   3   ?)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%------------------------------------------------------------------------------
fof(testcase_conclusion_fullish_002_Existential_Blank_Nodes,conjecture,
    ?[BNODE_x,BNODE_y] :
      ( iext(uri_ex_p,BNODE_x,BNODE_y)
      & iext(uri_ex_q,BNODE_y,BNODE_x) ) ).

fof(testcase_premise_fullish_002_Existential_Blank_Nodes,axiom,
    ?[BNODE_o] :
      ( iext(uri_ex_p,uri_ex_s,BNODE_o)
      & iext(uri_ex_q,BNODE_o,uri_ex_s) ) ).

%------------------------------------------------------------------------------
