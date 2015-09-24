grammar gia:concretesyntax;

closed nonterminal Expr with ast<abs:Expr>, pp, location;

concrete productions e::Expr
| 'none'
  {
    e.ast = abs:noneLiteral(location=e.location);
    e.pp = text("none");
  }
| '_'
  {
    e.ast = abs:wildcardLiteral(location=e.location);
    e.pp = text("_");
  }
| i::IntConstant_t
  {
    e.ast = abs:intLiteral(toInt(i.lexeme), location=e.location);
    e.pp = text(i.lexeme);
  }
| s::StringConstant_t
  {
    e.ast = abs:strLiteral(substring(1, length(s.lexeme) - 1, s.lexeme), location=e.location);
    e.pp = text(s.lexeme);
  }
| n::Id_t
  {
    e.ast = abs:nameLiteral(abs:name(n.lexeme, location=n.location), location=e.location);
    e.pp = text(n.lexeme);
  }
| '@' e1::Expr
  {
    e.ast = abs:capture(e1.ast, location=e.location);
    e.pp = cat(text("@"), e1.pp);
  }
| f::Expr LALParen_t args::Exprs ')'
  {
    e.ast = abs:app(f.ast, args.ast, location=e.location);
    e.pp = concat([f.pp, text("("), args.pp, text(")")]);
  }
| 'fn' '(' params::Params ')' '(' body::Expr ')'
  {
    e.ast = abs:lambdaExpr(params.ast, body.ast, location=e.location);
    e.pp = concat([text("fn (<params>)"), text("("), body.pp, text(")")]); -- TODO
  }
| e1::Expr '+' e2::Expr
  {
    e.ast = abs:addOp(e1.ast, e2.ast, location=e.location);
    e.pp = concat([e1.pp, text("+"), e2.pp]);
  }
| e1::Expr '&' e2::Expr
  {
    e.ast = abs:andOp(e1.ast, e2.ast, location=e.location);
    e.pp = concat([e1.pp, text("&"), e2.pp]);
  }
| e1::Expr '|' e2::Expr
  {
    e.ast = abs:orOp(e1.ast, e2.ast, location=e.location);
    e.pp = concat([e1.pp, text("|"), e2.pp]);
  }
| e1::Expr '~' e2::Expr
  {
    e.ast = abs:matchOp(e1.ast, e2.ast, location=e.location);
    e.pp = concat([e1.pp, text("~"), e2.pp]);
  }
| e1::Expr '.' n::Id_t
  {
    e.ast = abs:accessOp(e1.ast, abs:name(n.lexeme, location=n.location), location=e.location);
    e.pp = concat([e1.pp, text("."), text(n.lexeme)]);
  }
| e1::Expr '::' e2::Expr
  {
    e.ast = abs:consList(e1.ast, e2.ast, location=e.location);
    e.pp = concat([e1.pp, text("::"), e2.pp]);
  }
| 'if' cnd::Expr 'then' th::Expr 'else' el::Expr
  {
    e.ast = abs:cond(cnd.ast, th.ast, el.ast, location=e.location);
    e.pp = concat([text("if"), cnd.pp, text("then"), th.pp, text("else"), el.pp]);
  }
| e1::Expr LALBracket_t e2::Exprs ']'
  {
    e.ast = error("Not yet implemented");
    e.pp = concat([e1.pp, text("["), e2.pp, text("]")]);
  }
| '[' el::Exprs ']'
  {
    e.ast = abs:constructList(el.ast, location=e.location);
    e.pp = concat([text("["), el.pp, text("]")]);
  }
| '(' e1::Expr ')'
  {
    e.ast = e1.ast;
    e.pp = concat([text("("), e1.pp, text(")")]);
  }

closed nonterminal Exprs with ast<abs:Exprs>, pp;

concrete productions e::Exprs
| h::Expr ',' t::Exprs
  {
    e.ast = abs:consExpr(h.ast, t.ast);
    e.pp = concat([h.pp, text(","), t.pp]);
  }
| h::Expr
  {
    e.ast = abs:consExpr(h.ast, abs:nilExpr());
    e.pp = h.pp;
  }
|
  {
    e.ast = abs:nilExpr();
    e.pp = text("");
  }