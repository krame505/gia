grammar gia:concretesyntax;

closed nonterminal Expr with ast<abs:Expr>, location;

concrete productions e::Expr
| 'none'
  {
    e.ast = abs:noneLiteral(location=e.location);
  }
| '_'
  {
    e.ast = abs:wildcardLiteral(location=e.location);
  }
| i::IntConstant_t
  {
    e.ast = abs:intLiteral(toInt(i.lexeme), location=e.location);
  }
| s::StringConstant_t
  {
    e.ast = abs:strLiteral(substring(1, length(s.lexeme) - 2, s.lexeme), location=e.location);
  }
| n::Id_t
  {
    e.ast = abs:nameLiteral(abs:name(n.lexeme, location=n.location), location=e.location);
  }
| '@' e1::Expr
  {
    e.ast = abs:capture(e1.ast, location=e.location);
  }
| f::Expr '(' args::Exprs ')'
  {
    e.ast = abs:app(f.ast, args.ast, location=e.location);
  }
| 'fn' '(' params::Params ')' '(' body::Expr ')'
  {
    e.ast = abs:lambdaExpr(params.ast, body.ast, location=e.location);
  }
| e1::Expr '+' e2::Expr
  {
    e.ast = abs:addOp(e1.ast, e2.ast, location=e.location);
  }
| e1::Expr '&' e2::Expr
  {
    e.ast = abs:andOp(e1.ast, e2.ast, location=e.location);
  }
| e1::Expr '|' e2::Expr
  {
    e.ast = abs:orOp(e1.ast, e2.ast, location=e.location);
  }
| e1::Expr '~' e2::Expr
  {
    e.ast = abs:matchOp(e1.ast, e2.ast, location=e.location);
  }
| e1::Expr '~' n::Id_t
  {
    e.ast = abs:accessOp(e1.ast, abs:name(n.lexeme, location=n.location), location=e.location);
  }
| e1::Expr '::' e2::Expr
  {
    e.ast = abs:consList(e1.ast, e2.ast, location=e.location);
  }
| 'if' cnd::Expr 'then' th::Expr 'else' el::Expr
  {
    e.ast = abs:cond(cnd.ast, th.ast, el.ast, location=e.location);
  }
| '(' el::Exprs ')'
  {
    e.ast = abs:constructList(el.ast, location=e.location);
  }

closed nonterminal Exprs with ast<abs:Exprs>;

concrete production consExpr
e::Exprs ::= h::Expr ',' t::Exprs
{
  e.ast = abs:consExpr(h.ast, t.ast);
}

concrete production nilExpr
e::Exprs ::= 
{
  e.ast = abs:nilExpr();
}