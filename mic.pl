:- module(mic,[metainterpret/2,
               metainterpret/3,
               isa_atom/1,
               isa_integer/1,
               isa_string/1]).

:- use_module(library(list_util), [xfy_list/3]).
:- use_module(library(pprint), [print_term/2]).

/* <module> Metainterpertation critic 
 * 
 * mic gives us some information as to causes of failure for a restricted subset of 
 * prolog in which ';' is interpreted as exclusive disjunction.
 * 
 * From the error tree, which is a kind of recording of the failed SLD tree, we can 
 * then determine a likely target for "most interesting failure", for instance 
 * by looking for those resolution paths of greatest depth.
 * 
 * This library is useful for creating either an ad-hoc type-checker which 
 * verifies syntax of a term (well-formedness conditions etc.) or for creating 
 * a full fledged type checker. 
 *
 * @Author: Gavin Mendel-Gleason
 * @Copyright: Datachemist Ltd. 
 * @Licence: Apache License 2.0
 */

/**********************
 * Types
 * 
 * The following types are used in the metainterpreter:
 *
 * :- type error_tree ---> error_leaf(any,atom) ; error_branch(any,atom,list(error_tree))
 * :- type maybe(T) ---> just(T) ; none.
 *
 */

/**********************
 * Primitive type predicates 
 * 
 * Gives the base types which can be checked by the checker, 
 * prefixed by 'isa_' with the expectation that we will call this for 
 * user-defined types.
 */
isa_integer(X) :-
    integer(X).

isa_atom(X) :-
    atom(X).

isa_string(X) :-
    string(X).

/* 
 * metainterpret(Term,MaybeError:maybe(domain_error)) is det.
 * 
 * Metainterpret/2 does not fail, but rather keeps information about 
 * why it *would* fail under normal circumstances.
 */
metainterpret(MTerm, ME) :-
    strip_module(MTerm, M, Term),
    metainterpret(M, Term, ME).

/* 
 * metainterpret(Module,Term,MaybeError:maybe(domain_error)) is det.
 * 
 * Metainterpret/3 does the heavy lifting. We need to know what module 
 * context in which we'd like the term to be evaluated in order that 
 * we can ensure access to the various clauses etc.
 */
metainterpret(_, true, none).
metainterpret(M, \+ T, ME) :-
    (   \+ metainterpret(M, T,_)
    ->  ME = none
    ;   ME = just(error_leaf(\+ T,M)),
        format(atom(M), 'The negation ~q was not successful.', [\+ T])
    ).
metainterpret(_, isa_integer(X), ME) :-
    (   integer(X)
    ->  ME = none
    ;   ME = just(error_leaf(X, M)), 
        format(atom(M), '~q is not an integer', [X])
    ).
metainterpret(_, isa_atom(X), ME) :-
    (   atom(X)
    ->  ME = none
    ;   ME = just(error_leaf(X, M)), 
        format(atom(M), '~q is not an atom', [X])
    ).
metainterpret(_, isa_string(X), ME) :-
    (   string(X)
    ->  ME = none
    ;   ME = just(error_leaf(X, M)), 
        format(atom(M), '~q is not a string', [X])
    ).
metainterpret(M, (TP1,TP2), ME) :-
    metainterpret(M,TP1,ME1),
    metainterpret(M,TP2,ME2),
    (   ME1 = none,
        ME2 = none
    ->  ME = none
    ;   ME1 = none
    ->  ME2 = just(E2),
        ME = just(error_branch(TP2, Msg, [E2])),
        pprint(TP2,TP2A),
        format(atom(Msg), 'Right conjuct fails: ~w', [TP2A])
    ;   ME2 = none
    ->  ME1 = just(E1),
        ME = just(error_branch(TP1, Msg, [E1])),
        pprint(TP1,TP1A),
        format(atom(Msg), 'Left conjuct fails: ~w', [TP1A])
    ;   ME1 = just(E1),
        ME2 = just(E2),
        ME = just(error_branch((TP1,TP2), Msg, [E1,E2])),
        pprint(TP1,TP1A),
        pprint(TP2,TP2A),
        format(atom(Msg), 'Both conjuncts fail: ~w and ~w', [TP1A,TP2A])
    ).
metainterpret(M, (TP1->TP2), ME) :-
    !,
    metainterpret(M, TP1, ME1),
    (   ME1 = none
    ->  metainterpret(M, TP2, ME2),
        (   ME2 = none
        ->  ME = none
        ;   ME2 = just(E2),
            ME = just(error_branch((TP1->TP2), Msg, [E2])),
            pprint(TP2,TP2A),
            format(atom(Msg), 'Consequent fails: ~w', [TP2A])
        )
    ;   ME1 = just(E1),
        ME = just(error_branch((TP1->TP2), Msg, [E1])),
        pprint(TP1,TP1A),
        format(atom(Msg), 'Antecedent fails: ~w', [TP1A])
    ).
metainterpret(M, (TP1;TP2), ME) :-
    metainterpret(M, TP1,ME1),
    metainterpret(M, TP2,ME2),
    (   ME1=just(E1),
        ME2=just(E2)
    ->  ME = just(error_branch((TP1;TP2), M, [E1,E2])),
        format(atom(M), 'No viable clauses for disjunction ~q',
               [(TP1;TP2)])
    ;   ME1=none,
        ME2=none
    ->  ME = just(error_leaf((TP1;TP2),M)),
        format(atom(M),'Too many successful clauses for disjunction ~q',
               [(TP1;TP2)])
    ;   ME=none
    ).
metainterpret(_, (TP1=TP2), ME) :-
    (   TP1=TP2
    ->  ME=none
    ;   ME = just(error_leaf((TP1=TP2),Msg)),
        format(atom(Msg), 'Non unifiable term elements ~q and ~q', [TP1,TP2])
    ).
metainterpret(M, P, ME) :-
    functor(P,F,N),
    \+ member(F,[isa,isa_integer,isa_atom,isa_string,',',';', '=', true]),
    !,
    length(Vars,N),
    P =.. [F|Args],
    Q =.. [F|Vars],

    (   predicate_property(M:P, visible)
    ->  Module = M
    ;   predicate_property(M:P, imported_from(Local_M))
    ->  Module = Local_M
    ;   context_module(Ctx_M),
        Module = Ctx_M
    ),
    
    bagof(ME_i-Body,(clause(Module:Q, Body),
                     (   Vars = Args
                     ->  metainterpret(M,Body,ME_i)
                     ;   ME_i = just(error_leaf((Vars=Args),M)),
                         format(atom(M), 'Head ~q does not match arguments ~q', [Q,Args])
                     )
                    ),
          MEs),
    
    include([none-_]>>(true), MEs, Successes),
    maplist([_-Body,Body]>>(true), Successes, Bodies),        
    include([just(E)-_]>>(true), MEs, Just_Failures),
    maplist([just(E)-_,E]>>(true), Just_Failures, Failures),

    (   MEs = []
    ->  ME = just(error_leaf(P,Msg)),
        format(atom(Msg),'No predicate ~q defined', [F/N])
    ;   Successes = []
    ->  ME = just(error_branch(P,Msg,Failures)),
        format(atom(Msg), 'No successful clause for predicate ~q', [P])
    ;   Successes = [_,_|_]
    ->  xfy_list(';',Definition,Bodies),        
        ME = just(error_leaf(P:-Definition, Msg)),
        pprint(Definition,Def_Atom),
        format(atom(Msg), 'Too many viable clauses for predicate ~w:~n ~w',
               [P,Def_Atom])
    ;   ME = none
    ).

/* 
 * stacks(Error:error, Stack:list(pair(any,atom))) is nondet. 
 *
 * Finds each stack of an error.
 */
stacks(error_leaf(T,M),[T-M]).
stacks(error_branch(T,M,L),[T-M|S]) :-
    member(E,L),
    stacks(E,S).

/*  
 * deepest(Error:error,Stack:list(error)) is semidet.
 */
deepest(Error,Stack) :- 
    bagof(S-N, (stacks(Error,S), length(S,N)), Stacks),
    predsort([C,_-N1,_-N2]>>(compare(C,N1,N2)), Stacks, [Stack-_|_]).

/* 
 * write_stack(Stack:list(error))
 */
write_stack(Stack) :-
    reverse(Stack,Rev),
    forall(member(_-M,Rev),
           (   nl,
               write(M)
           )).

/* 
 * pprint(Term:any,Atom:atom) is det.
 * 
 * Pretty print term to atom
 */ 
pprint(Term,Atom) :-
    with_output_to(
        atom(Atom),
        (   current_output(Stream), 
            print_term(Term, [indent_arguments(true),output(Stream)])
        )
    ).

/* 
 * We can use the above metainterpreter to implement HM style type checking 
 * with something along the following lines. 

:- type list(T) --> [] ; [T|list(T)].

isa_list(X,T) :-
    (  X = []
    ;  X = [H|R],
       isa(H,T),
       isa_list(R,T)
    ).

isa(X,T) :-
    var(T),
    !,
    when(T,
         isa(X,T)).
isa(X,T) :-
    T =.. [F|Args],
    atom_concat('isa_',F,G),
    Goal =.. [G,X|Args],
    call(Goal).

 */
