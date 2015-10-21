grammar gia:abstractsyntax;

synthesized attribute rules::[Pair<String Expr>];
synthesized attribute returnExpr::Maybe<Expr>;
synthesized attribute returnValue::Maybe<Value>;

nonterminal Decls with env, defs, errors, rules, returnExpr, returnValue, evalExpr, evalRes, evalResType, evalErrors;

abstract production consDecl
d::Decls ::= h::Decl t::Decls
{
  d.errors := h.errors ++ t.errors;
  d.defs = h.defs ++ t.defs;
  h.env = addEnv(d.defs, d.env);
  t.env = addEnv(h.defs, d.env);
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

nonterminal Decl with env, defs, rules, errors, location;

abstract production decls
d::Decl ::= ds::Decls
{
  d.errors := ds.errors;
  d.defs = ds.defs;
  d.rules = ds.rules;
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
  d.errors :=
    case te.type of
      structureType(fields) -> []
    | t -> [err(te.location, s"Type in datatype declaration must be a structure, but got ${show(80, t.pp)}")]
    end ++ te.errors;
  d.defs = [];
  d.rules = [];
}

abstract production valDecl
d::Decl ::= n::Name mte::MaybeTypeExpr e::Expr
{
  d.errors := e.errors;
  d.defs = [pair(n.name, val:lazyValue(d.env, d.typeNameEnv, e))];
  d.rules = [pair(n.name, e)];
}

abstract production nodeDecl
d::Decl ::= n::Name p::Params mte::MaybeTypeExpr b::Decls
{
  d.errors := p.errors ++ mte.errors ++ b.errors;
  d.defs = [pair(n.name, val:functionValue(n.name, d.env, p.types, if b.returnType.isJust then b.returnType.fromJust else anyType(), p.names, b))];
  d.rules =
    case b.returnExpr of
      just(e) -> [pair(n.name, lambdaExpr(p, letExpr(b, e, location=d.location), location=d.location))]
    | nothing() -> []
    end;
  
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