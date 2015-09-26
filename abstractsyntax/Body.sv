grammar gia:abstractsyntax;

synthesized attribute rules::[Pair<String Expr>];
synthesized attribute returnValue::Maybe<Value>;

nonterminal Body with env, defs, errors, rules, returnValue, location;

abstract production consEquations
b::Body ::= h::Equation t::Body
{
  b.errors := h.errors ++ t.errors;
  b.defs = h.defs ++ t.defs;
  h.env = addEnv(b.defs, b.env);
  t.env = addEnv(h.defs, b.env);
  b.rules = h.rules ++ t.rules;
  b.returnValue = t.returnValue;
}

abstract production returnBody
b::Body ::= e::Expr
{
  b.errors := e.errors;
  b.defs = [];
  b.rules = [];
  b.returnValue = just(e.value);
}

abstract production nilBody
b::Body ::=
{
  b.errors := [];
  b.defs = [];
  b.rules = [];
  b.returnValue = nothing();
}

nonterminal Equation with env, defs, errors, rules, location;

abstract production equation
eq::Equation ::= n::Name e::Expr
{
  eq.errors := e.errors;
  eq.defs = [pair(n.name, val:lazyValue(eq.env, e))];
  eq.rules = [pair(n.name, e)];
}

