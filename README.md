# Typo

Typo is a type and syntax checker reporting tool using metainterpretation.

## Metainterpertation critic 

The metainterpertation critic (metainterpret/2) gives us information
as to causes of failure for a restricted subset of prolog in which ';'
is interpreted as exclusive disjunction.

From the error tree, which is a kind of recording of the failed SLD
tree, we can then determine a likely target for "most interesting
failure", for instance by looking for those resolution paths of
greatest depth.

This library is useful for creating either an ad-hoc type-checker
which verifies syntax of a term (well-formedness conditions etc.) or
for creating a full fledged type checker.

Author: Gavin Mendel-Gleason
Copyright: Datachemist Ltd. 
Licence: Apache License 2.0
