grammar gia:abstractsyntax;

nonterminal Decls with env, defs, errors, evalExpr, evalRes, evalResType, evalErrors;

abstract production consDecl
d::Decls ::= h::Decl t::Decls
{
  d.errors := h.errors ++ t.errors;
  d.defs = h.defs ++ t.defs;
  t.env = addEnv(h.defs, d.env);
  d.evalRes = t.evalRes;
  d.evalResType = t.evalResType;
  d.evalErrors = t.evalErrors;
}

abstract production nilDecl
d::Decls ::= 
{
  d.errors := [];
  d.defs = [];
  
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

nonterminal Decl with env, defs, errors, location;

abstract production decls
d::Decl ::= ds::Decls
{
  d.errors := ds.errors;
  d.defs = ds.defs;
}

abstract production typeDecl
d::Decl ::= n::Name te::TypeExpr
{
  d.errors := te.errors;
  d.defs = [];
}

abstract production dataTypeDecl
d::Decl ::= n::Name te::TypeExpr extends::Maybe<TypeExpr>
{
  d.errors :=
    case te.type of
      structureType(fields) -> []
    | t -> [err(te.location, s"Type in datatype declaration must be a structure, but got ${show(80, t.pp)}")]
    end ++ te.errors;
  d.defs = [];
}

abstract production valDecl
d::Decl ::= n::Name e::Expr
{
  d.errors := e.errors;
  d.defs = [pair(n.name, val:lazyValue(d.env, e))];
}

abstract production nodeDecl
d::Decl ::= n::Name p::Params mte::MaybeTypeExpr b::Body
{
  d.errors := p.errors ++ mte.errors ++ b.errors;
  d.defs = [pair(n.name, val:functionValue(n.name, d.env, p, b))];
  
  -- Dummy values provided for error checking
  p.args = [];
  b.env = addEnv(p.defs ++ d.defs, d.env);
}

inherited attribute args::[val:Value];
nonterminal Params with env, defs, errors, pp, args, len;

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
  p.len = t.len + 1;
}

abstract production nilParam
p::Params ::= 
{
  p.errors := [];
  p.pp = text("");
  p.defs = [];
  p.len = 0;
}