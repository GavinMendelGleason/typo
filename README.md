# Typo

Typo is a type and syntax checker reporting tool using metainterpretation.

## Metainterpertation critic 

The metainterpertation critic (`metainterpret/2` or `metainterpret/3`)
gives us information as to causes of failure for a restricted subset
of prolog in which `;` is interpreted as exclusive disjunction.

From the error tree, which is a kind of recording of the failed SLD
tree, we can then determine a likely target for "most interesting
failure", for instance by looking for those resolution paths of
greatest depth.

This library is useful for creating either an ad-hoc type-checker
which verifies syntax of a term (well-formedness conditions etc.) or
for creating a full fledged type checker.

## Invocation 

In order to invoke the metainterpretation critic, simply write down
some syntax checking predicates and you can use `metainterpret/3` to
invoke them. For instance, given the following programme: 

```
isa_integer_list([]). 
isa_integer_list([H|T]) :- 
    isa_integer(H),
    isa_integer_list(T).
```


```
-? metainterpret(user, isa_integer_list([1,2,3]), ME).

ME = none.
```

The metainterpreter will bind ME to a `maybe(error)` type: 

```
:- type maybe(T) ---> none ; just(T).
```

resulting in `none` if there is no error, and `just(Error)` if there is 
one (or many). The Error type is: 

```
:- type error ---> error_leaf(any,atom) ; error_branch(any,atom,list(error)).
```

We can extract a likely cause of the failure by looking at the deepest
branch of the error tree, which can be extracted with `deepest/2` which extracts a stack 
of errors and it can be printed with `write_stack/1` as follows: 

```
:- metainterpret(user, isa_integer_list([1,2,x]), just(Error)), deepest(Error,Stack), write_stack(Stack).

x is not an integer
Left conjuct fails: isa_integer(x)
No successful clause for predicate isa_int_list([x])
Right conjuct fails: isa_int_list([ x ])
No successful clause for predicate isa_int_list([2,x])
Right conjuct fails: isa_int_list([ 2, x ])
No successful clause for predicate isa_int_list([1,2,x])

...
```

Author: Gavin Mendel-Gleason

Copyright: Datachemist Ltd. 

Licence: Apache License 2.0
