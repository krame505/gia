grammar gia:abstractsyntax;

synthesized attribute rules::[Pair<String Expr>];
synthesized attribute fnErrors::[Message] with ++;

nonterminal Body with env, errors, fnErrors, rules, location;

abstract production consEquations
b::Body ::= h::Equation t::Body
{
  b.errors := h.errors ++ t.errors;
  b.fnErrors := t.fnErrors;
  b.rules = h.rules ++ t.rules;
}

abstract production returnBody
b::Body ::= e::Expr
{
  b.errors := [err(b.location, "Unexpected return in non-function")];
  b.fnErrors := e.errors;
  b.rules = [];
}

abstract production nilBody
b::Body ::=
{
  b.errors := [];
  b.fnErrors := [];
  b.rules = [];
}

nonterminal Equation with env, errors, rules, location;

abstract production equation
eq::Equation ::= n::Name e::Expr
{
  eq.errors := e.errors;
  eq.rules = [pair(n.name, e)];
}

