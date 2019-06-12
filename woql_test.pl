:- module(woql_test,[wf/1,
                     nmi/2,
                     op(600, xfx, <:)]).

:- op(2, xfx, :).
:- op(2, xfx, :=).
:- op(600, xfx, <:).

:- use_module(mic).

/*
 * Variables
 * 
 * V := v(atom)
 */
ovar(v(I)) :-
    isa_atom(I).

/*
 * Rigid Identifiers 
 *
 * R := R / atom | atom
 */ 
rigid_identifier(ID / Suffix) :-
    rigid_identifier(ID),
    isa_atom(Suffix).
rigid_identifier(ID) :-
    isa_atom(ID).
    
/*
 * Identifiers 
 *
 * I := R | V
 */ 
identifier(ID) :-
    rigid_identifier(ID).
identifier(ID) :-
    ovar(ID).

/* 
 * Class 
 * 
 * C := I
 * 
 * Currently no class expressions
 */ 
class(C) :-
    identifier(C).

/*
 * Objects  
 * 
 * O := I:C | I
 */ 
obj(ID:Class) :-
    identifier(ID),
    class(Class).
obj(ID) :-
    identifier(ID).

/* 
 * Graph 
 * 
 * G := I
 */
graph_term(G) :-
    identifier(G).

/*
 * Literals
 *  
 * L := l(I,string)
 */ 
lit(l(Type,S)) :-
    identifier(Type),
    identifier(S).

/*
 * OL := O | L
 */ 
obj_or_lit(X) :-
    obj(X).
obj_or_lit(X) :-
    lit(X).

/* 
 * R := obj
 */ 
relationship(R) :-
    obj(R).

/* 
 * AL := 
 *
 */
arg_list([A|Rest]) :-
    obj_or_lit(A),
    arg_list(Rest).
arg_list([]).

/* 
 * 
 * 
 */
value(V) :-
    isa_atom(V).
value(V) :-
    string(V).
value(V) :-
    integer(V).
value(V) :-
    ovar(V).
value(V) :-
    number(V).

/*
 * Conjunctive Patterns
 * 
 * K := t(X,R,Y) | q(X,R,Y,G) | K,K | L op L | like(A,B,N) | true
 * op in =, <, >, :, <<
 */
con_pattern(A = B) :-
    value(A),
    value(B).
con_pattern(A < B) :-
    value(A),
    value(B).
con_pattern(A > B) :-
    value(A),
    value(B).
con_pattern(A : B) :-
    obj(A : B).
con_pattern(A << B) :-
    class(A),
    class(B).
con_pattern(like(A,B,F)) :-
    value(A),
    value(B),
    value(F).
con_pattern(p(A,Args)) :-
    isa_atom(A),
    arg_list(Args).
con_pattern(t(X,P,R)) :-
    obj(X),
    obj(P),
    obj_or_lit(R).
con_pattern(t(X,P,R,G)) :-
    obj(X),
    obj(P),
    obj_or_lit(R),
    graph_term(G).
con_pattern(r(X,P,R)) :-
    obj(X),
    relationship(P),
    obj_or_lit(R).
con_pattern(r(X,P,R,G)) :-
    obj(X),
    relationship(P),
    obj_or_lit(R),
    graph_term(G).
con_pattern(opt(T)) :-
    con_pattern(T).
con_pattern((P,Q)) :-
    con_pattern(P),
    con_pattern(Q).
con_pattern(true).

/*
 * Patterns 
 *
 * P := K | P;P | P,P
 * 
 */
pattern(P) :-
    con_pattern(P).
pattern((P;Q)) :-
    pattern(P),
    pattern(Q).
pattern((P,Q)) :-
    pattern(P),
    pattern(Q).

/*
 * variable list
 *  
 * VL := [] | [V|VL]
 */
var_list([]).
var_list([V|VL]) :-
    ovar(V),
    var_list(VL).

/*
 * Select
 *
 * S := select(VL,P)
 */ 
select(VL,P) :-
    var_list(VL),
    pattern(P).

/*
 * all 
 * 
 * A := all(P)
 */
all(P) :-
    %var_list(VL),
    pattern(P).

/*
 * any
 * 
 * E := any(VL,P)
 */
any(VL,P) :-
    var_list(VL),
    pattern(P).


/* 
 * source
 * 
 * S := id | file(id,type)
 */
source(Term) :-
    rigid_identifier(Term).
source(file(Id,Type)) :-
    isa_atom(Id),
    isa_atom(Type).

/* Prefixes 
 * 
 * PF := list(atom = atom)
 */
prefixes([]).
prefixes([P=U|Rest]) :-
    isa_atom(P),
    isa_atom(U),
    prefixes(Rest).

/*
 * Well formed term
 * 
 * WF := S | A | E | let(atom,P,WF)
 */ 
wf(any(VL,P)) :-
    any(VL,P).
wf(all(S)) :-
    all(S).
wf(select(S,T)) :-
    select(S,T).
wf(from(P,S)) :-
    source(P),
    wf(S).
wf(where(S)) :-
    pattern(S).
wf(let(P,Args,Def,S)) :-
    isa_atom(P),
    var_list(Args),
    pattern(Def),
    wf(S).
wf(depth(N,S)) :-
    integer(N),
    wf(S).
wf(prefixes(PS,S)) :-
    prefixes(PS),
    wf(S).
wf(start(N,S)) :-
    integer(N),
    wf(S).
wf(limit(N,S)) :-
    integer(N),
    wf(S).
