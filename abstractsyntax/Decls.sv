grammar gia:abstractsyntax;

synthesized attribute rules::[Pair<String Expr>];
synthesized attribute returnExpr::Maybe<Expr>;
synthesized attribute returnValue::Maybe<Value>;

nonterminal Decls with env, nonRecEnv, defs, errors, rules, returnExpr, returnValue, evalExpr, evalRes, evalResType, evalErrors;

abstract production consDecl
d::Decls ::= h::Decl t::Decls
{
  d.errors := h.errors ++ t.errors;
  d.defs = h.defs ++ t.defs;
  h.env = addEnv(d.defs, d.env);
  t.env = addEnv(h.defs, d.env);
  t.nonRecEnv = addEnv(h.defs, d.nonRecEnv);
  d.rules = h.rules ++ t.rules;
  d.returnExpr = t.returnExpr;
  d.returnValue = t.returnValue;
  d.evalRes = t.evalRes;
  d.evalResType = t.evalResType;
  d.evalErrors = t.evalErrors;
}

abstract production nilDecl
d::Decls ::= 
{
  d.errors := [];
  d.defs = [];
  d.rules = [];
  d.returnExpr = nothing();
  d.returnValue = nothing();
  
  local evalExpr::Expr = d.evalExpr;
  evalExpr.env = d.env;
  evalExpr.typeEnv = d.typeEnv;
  evalExpr.typeNameEnv = d.typeNameEnv;
  
  d.evalRes =
    if null(evalExpr.errors)
    then evalExpr.value
    else val:errorValue(evalExpr.errors);
  d.evalResType = evalExpr.type;
  d.evalErrors = evalExpr.errors;
}

abstract production returnDecl
d::Decls ::= e::Expr
{
  d.errors := e.errors;
  d.returnExpr = just(e);
  d.returnValue = just(e.value);
  
  forwards to nilDecl();
}

abstract production parseErrorDecls
d::Decls ::= errorTxt::String
{
  d.errors := [err(loc("", -1, -1, -1, -1, -1, -1), errorTxt)];
  d.defs = [];
  d.evalRes = error("evalRes demanded from parseErrorDecls");
  d.evalResType = error("evalResType demanded from parseErrorDecls");
  d.evalErrors = error("evalErrors demanded from parseErrorDecls");
  
  forwards to nilDecl();
}

nonterminal Decl with env, nonRecEnv, defs, rules, errors, location;

abstract production decls
d::Decl ::= ds::Decls
{
  d.errors := ds.errors;
  d.defs = ds.defs;
  d.rules = ds.rules;
}

abstract production openDecl
d::Decl ::= e::Expr
{
  d.errors := e.errors;
  e.env = d.nonRecEnv;
  
  forwards to
    case e.value of
      structureValue(ds) -> decls(convertValDecls(ds), location=d.location)
    | nodeValue(_, _, _, ds) -> decls(convertValDecls(ds), location=d.location)
    end
  with {env = emptyEnv();};
}

function convertValDecls
Decls ::= ds::[Pair<String Value>]
{
  return
    if null(ds)
    then nilDecl()
    else
      consDecl(
        valDecl(
          name(head(ds).fst, location=bogusLocation),
          justTypeExpr(directTypeExpr(head(ds).snd.type, location=bogusLocation), location=bogusLocation),
          valueExpr(head(ds).snd, location=bogusLocation), location=bogusLocation),
        convertValDecls(tail(ds)));
}

abstract production typeDecl
d::Decl ::= n::Name te::TypeExpr
{
  d.errors := te.errors;
  d.defs = [];
  d.rules = [];
}

abstract production dataTypeDecl
d::Decl ::= n::Name te::TypeExpr extends::TypeExpr
{
  d.errors := te.errors;
  d.defs = [];
  d.rules = [];
}

abstract production valDecl
d::Decl ::= n::Name mte::MaybeTypeExpr e::Expr
{
  d.errors := e.errors;
  
  local runtimeErrors::[Message] = convertTypeErrors(e.value.type, mte.type, "value declaration", d.location);
  d.defs = [pair(n.name, val:lazyValue(d.env, d.typeNameEnv, e))];
    --if null(runtimeErrors)
    --then [pair(n.name, val:lazyValue(d.env, d.typeNameEnv, e))]
    --else [pair(n.name, val:errorValue(runtimeErrors))];
  d.rules = [pair(n.name, e)];
}

abstract production nodeDecl
d::Decl ::= n::Name p::Params mte::MaybeTypeExpr b::Expr
{
  d.errors := p.errors ++ mte.errors ++ b.errors;
  d.defs = [pair(n.name, val:functionValue(n.name, d.env, d.typeEnv, p.types, mte.type, p.names, b))];
  d.rules = [pair(n.name, lambdaExpr(p, b, location=d.location))];
  
  -- Dummy values provided for error checking
  p.args = [];
  b.env = addEnv(p.defs ++ [pair("self", falseValue())], d.env);
}

inherited attribute args::[val:Value];
synthesized attribute names::[String];
nonterminal Params with env, defs, names, errors, pp, args, len;

abstract production consParam
p::Params ::= h::Name mte::MaybeTypeExpr t::Params
{
  p.errors :=
    (if containsBy(stringEq, h.name, map(fst, t.defs))
     then [err(h.location, "Duplicate parameter " ++ h.name)]
     else []) ++ mte.errors ++ t.errors;
  
  p.pp = if t.len > 0 then concat([h.pp, text(", "), t.pp]) else h.pp;
  
  local callValue::val:Value = if null(p.args) then val:falseValue() else head(p.args);
  t.args = if null(p.args) then [] else tail(p.args);
  p.defs = pair(h.name, callValue) :: t.defs;
  p.names = h.name :: t.names;
  p.len = t.len + 1;
}

abstract production nilParam
p::Params ::= 
{
  p.errors := [];
  p.pp = text("");
  p.defs = [];
  p.names = [];
  p.len = 0;
}