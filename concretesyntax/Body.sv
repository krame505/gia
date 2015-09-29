grammar gia:concretesyntax;

closed nonterminal Body with ast<abs:Body>, location;

concrete production consEquations
b::Body ::= h::Equation t::Body
{
  b.ast = abs:consEquations(h.ast, t.ast, location=b.location);
}

concrete production returnBody
b::Body ::= 'return' e::Expr ';'
{
  b.ast = abs:returnBody(e.ast, location=b.location);
}

concrete production nilBody
b::Body ::=
{
  b.ast = abs:nilBody(location=b.location);
}

closed nonterminal Equation with ast<abs:Equation>, location;

concrete production equation
eq::Equation ::= n::Id_t '=' e::Expr ';'
{
  eq.ast = abs:equation(abs:name(n.lexeme, location=n.location), e.ast, location=eq.location);
}

