grammar gia:abstractsyntax;

nonterminal Decls with env, defs, errors, evalExpr, evalRes;

abstract production consDecl
d::Decls ::= h::Decl t::Decls
{
  d.errors := h.errors ++ t.errors;
  d.defs = h.defs ++ t.defs;
  t.env = addEnv(h.defs, d.env);
  d.evalRes = t.evalRes;
}

abstract production nilDecl
d::Decls ::= 
{
  d.errors := [];
  d.defs = [];
  
  local evalExpr::Decorated Expr =
    decorate d.evalExpr with {env = d.env;};
  d.evalRes =
    if null(evalExpr.errors)
    then evalExpr.value
    else val:errorValue(evalExpr.errors);
}

abstract production parseErrorDecls
d::Decls ::= errorTxt::String
{
  d.errors := [err(loc("", -1, -1, -1, -1, -1, -1), errorTxt)];
  d.defs = [];
  d.evalRes = error("evalRes demanded from parseErrorDecls");
}

nonterminal Decl with env, defs, errors, location;

abstract production decls
d::Decl ::= ds::Decls
{
  d.errors := ds.errors;
  d.defs = ds.defs;
}

abstract production nodeDecl
d::Decl ::= n::Name p::Params b::Body
{
  d.errors := p.errors ++ b.errors;
  d.defs = [pair(n.name, valueItem(val:constructorValue(d.env, p, b.rules)))];
  
  -- Dummy values provided for error checking
  p.args = [];
  b.env = addEnv(p.defs, d.env);
}

{-
abstract production FunctionDecl
d::Decl ::= n::Name p::Params e::Expr
{
  d.errors := p.errors ++ e.errors;
}
-}

inherited attribute args::[val:Value];
nonterminal Params with env, defs, errors, pp, args, len, location;

abstract production consParam
p::Params ::= h::Name t::Params
{
  p.errors :=
    (if containsBy(stringEq, h.name, map(fst, t.defs))
     then [err(h.location, "Duplicate parameter " ++ h.name)]
     else []) ++ t.errors;
  
  p.pp = concat([h.pp, text(", "), t.pp]);
  
  local callValue::val:Value = if null(p.args) then val:noneValue() else head(p.args);
  t.args = if null(p.args) then [] else tail(p.args);
  p.defs = pair(h.name, valueItem(callValue)) :: t.defs;
  p.len = t.len + 1;
}

abstract production nilParam
p::Params ::= 
{
  p.errors := [];
  p.defs = [];
  p.len = 0;
}