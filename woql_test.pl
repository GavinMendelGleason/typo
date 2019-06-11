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
    !,
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
    \+ ID = _:_,
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
wf(from(G,S)) :-
    identifier(G),
    wf(S).
wf(depth(N,S)) :-
    integer(N),
    wf(S).
wf(prefixes(PS,S)) :- 
    exclude([P=U]>>(isa_atom(P),isa_atom(U)),PS,[]),
    wf(S).
wf(start(N,S)) :-
    integer(N),
    wf(S).
wf(limit(N,S)) :-
    integer(N),
    wf(S).

/* 
 * conjunction_to_list(A:term,L:list) is det.
 * 
 * converts a conjunction to a list
 */
conjunction_to_list((A,B),[A|C]) :-
    !,
    conjunction_to_list(B,C).
conjunction_to_list(C,[C]).

/* 
 * nmi(X,F) is nondet.
 * 
 * Negative Meta-Interpreter (NMI):
 *
 * This should find reasons for failure of syntactic expressions, by manipulating 
 * a more straight-forward "grammar" expressed as simple predicates.
 *
 */
nmi(X,F) :-
    conjunction_to_list(X,L),
    nmi_aux(L,F).

nmi_aux([], _) :-
    !,
    fail.
nmi_aux([true|T], F) :-
    !,
    nmi_aux(T,F).
nmi_aux((A;B), H) :-
    !,
    conjunction_to_list(A,LA),
    conjunction_to_list(B,LB),
    nmi_aux(LA,F),
    nmi_aux(LB,G),
    format(atom(M), 'Unable to succeed in finding any solution to ~q : ~q', [(A;B,(F;G))]),
    H = [type=error, message=M].
nmi_aux([Goal|Rest], H) :-
    \+ Goal = ( , ),
    Goal =.. [H|Terms],
    length(Terms,N),
    length(Vars,N),
    New_Goal =.. [H|Vars],
    bagof(Failure,(   clause(New_Goal, Body),
                      (   Vars = Terms,
                          conjunction_to_list(Body,LA),
                          append(LA,Rest,Stack),
                          nmi_aux(Stack,Failure)
                      ;   format(atom(M), 'Could not unify with Terms: ~q and Body: ~q', [Terms, Body]),
                          Failure = [type=error, message=M]
                      )
                  ), Failures),
    writeq(Failures),
    (   Failures = []
    ->  fail
    ;   format(atom(M), 'The following violations occurred: ~q', [Failures]),
        H = [type=error, message=M]).

/* 

nmi(wf(select([],true))).

*/
