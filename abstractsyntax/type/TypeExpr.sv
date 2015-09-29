grammar gia:abstractsyntax:type;

synthesized attribute type::Type occurs on Expr;

nonterminal TypeExpr with typeEnv, typeNameEnv, errors, type, location;

abstract production anyTypeExpr
te::TypeExpr ::=
{
  te.errors := [];
  te.type = anyType();
}

abstract production intTypeExpr
te::TypeExpr ::=
{
  te.errors := [];
  te.type = intType();
}

abstract production strTypeExpr
te::TypeExpr ::=
{
  te.errors := [];
  te.type = strType();
}

abstract production listTypeExpr
te::TypeExpr ::= te1::TypeExpr
{
  te.errors := te1.errors;
  te.type = listType(te1.type);
}

abstract production structureTypeExpr
te::TypeExpr ::= fields::[Pair<String TypeExpr>]
{
  local fieldTypeExprs::[Decorated TypeExpr] = map(decorateTypeExpr(te.typeEnv, te.typeNameEnv, _), map(snd, fields));
  te.errors := foldr(append, [], map((.errors), fieldTypeExprs));
  te.type = structureType(pairMap(pair, map(fst, fields), map((.type), fieldTypeExprs)));
}

abstract production functionTypeExpr
te::TypeExpr ::= params::[TypeExpr] ret::TypeExpr
{
  te.errors := ret.errors ++ foldr(append, [], map((.errors), params));
  te.type = functionType(map((.type), params), ret.type);
}

abstract production nameTypeExpr
te::TypeExpr ::= n::Name
{
  te.errors := n.typeNameLookupCheck;
  te.type = namedType(n, n.typeNameLookup);
}

function decorateTypeExpr
Decorated TypeExpr ::= typeEnv::TypeEnv typeNameEnv::TypeEnv te::TypeExpr
{
  return decorate te
         with {typeEnv = typeEnv;
               typeNameEnv = typeNameEnv;};
}

function pairMap
[c] ::= fn::(c ::= a b) l1::[a] l2::[b]
{
  return
    if null(l1) || null(l2)
    then []
    else fn(head(l1), head(l2)) :: pairMap(fn, tail(l1), tail(l2)); 
}

nonterminal MaybeTypeExpr with typeEnv, typeNameEnv, errors, type, isJust, location;

abstract production justTypeExpr
mte::MaybeTypeExpr ::= te::TypeExpr
{
  mte.errors := te.errors;
  mte.type = te.type;
  mte.isJust = true;
}

abstract production nothingTypeExpr
mte::MaybeTypeExpr ::= 
{
  mte.errors := [];
  mte.type = anyType();
  mte.isJust = false;
}