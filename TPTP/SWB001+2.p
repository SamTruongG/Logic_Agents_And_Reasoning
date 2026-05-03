%------------------------------------------------------------------------------
% File     : SWB001+2 : TPTP v9.2.1. Released v5.2.0.
% Domain   : Semantic Web
% Problem  : Subgraph Entailment
% Version  : [Sch11] axioms : Reduced > Incomplete.
% English  :

% Refs     : [Sch11] Schneider, M. (2011), Email to G. Sutcliffe
% Source   : [Sch11]
% Names    : 001_Subgraph_Entailment [Sch11]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.17 v6.0.0, 0.00 v5.3.0, 0.09 v5.2.0
% Syntax   : Number of formulae    :    2 (   0 unt;   0 def)
%            Number of atoms       :    6 (   0 equ)
%            Maximal formula atoms :    4 (   3 avg)
%            Number of connectives :    4 (   0   ~;   0   |;   4   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%            Maximal formula depth :    4 (   3 avg)
%            Maximal term depth    :    1 (   1 avg)
%            Number of predicates  :    1 (   1 usr;   0 prp; 3-3 aty)
%            Number of functors    :    9 (   9 usr;   9 con; 0-0 aty)
%            Number of variables   :    0 (   0   !;   0   ?)
% SPC      : FOF_THM_EPR_NEQ

% Comments :
%------------------------------------------------------------------------------
fof(testcase_conclusion_fullish_001_Subgraph_Entailment,conjecture,
    ( iext(uri_rdf_type,uri_ex_r,uri_owl_Restriction)
    & iext(uri_owl_onProperty,uri_ex_r,uri_ex_p) ) ).

fof(testcase_premise_fullish_001_Subgraph_Entailment,axiom,
    ( iext(uri_rdfs_subClassOf,uri_ex_c,uri_ex_r)
    & iext(uri_rdf_type,uri_ex_r,uri_owl_Restriction)
    & iext(uri_owl_onProperty,uri_ex_r,uri_ex_p)
    & iext(uri_owl_someValuesFrom,uri_ex_r,uri_ex_d) ) ).

%------------------------------------------------------------------------------
