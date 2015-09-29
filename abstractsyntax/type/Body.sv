grammar gia:abstractsyntax:type;

synthesized attribute ruleTypes::[Pair<String Type>] occurs on Body, Equation;
synthesized attribute returnType::Maybe<Type> occurs on Body;

aspect production consEquations
b::Body ::= h::Equation t::Body
{
  b.typeDefs = h.typeDefs ++ t.typeDefs;
  h.typeEnv = addEnv(b.typeDefs, b.typeEnv);
  t.typeEnv = addEnv(h.typeDefs, b.typeEnv);
  b.ruleTypes = h.ruleTypes ++ t.ruleTypes;
  b.returnType = t.returnType;
}

aspect production returnBody
b::Body ::= e::Expr
{
  b.typeDefs = [];
  b.ruleTypes = [];
  b.returnType = just(e.type);
}

aspect production nilBody
b::Body ::=
{
  b.typeDefs = [];
  b.ruleTypes = [];
  b.returnType = nothing();
}

aspect production equation
eq::Equation ::= n::Name e::Expr
{
  eq.typeDefs = [pair(n.name, anyType())]; -- TODO: Figure out a better fix for recursive type dependency
  eq.ruleTypes = [pair(n.name, anyType())];--e.type
}

