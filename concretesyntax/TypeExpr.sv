grammar gia:concretesyntax;

closed nonterminal TypeExpr with ast<abs:TypeExpr>, pp, location;

concrete productions te::TypeExpr
| 'any'
  {
    te.ast = abs:anyTypeExpr(location=te.location);
    te.pp = text("any");
  }
| 'bool'
  {
    te.ast = abs:boolTypeExpr(location=te.location);
    te.pp = text("bool");
  }
| 'int'
  {
    te.ast = abs:intTypeExpr(location=te.location);
    te.pp = text("int");
  }
| 'str'
  {
    te.ast = abs:strTypeExpr(location=te.location);
    te.pp = text("str");
  }
| te1::TypeExpr '*'
  {
    te.ast = abs:listTypeExpr(te1.ast, location=te.location);
    te.pp = pp"${te1.pp}*";
  }
| te1::TypeExpr '%'
  {
    te.ast = abs:setTypeExpr(te1.ast, location=te.location);
    te.pp = pp"${te1.pp}*";
  }
| te1::TypeExpr '?'
  {
    te.ast = abs:maybeTypeExpr(te1.ast, location=te.location);
    te.pp = pp"${te1.pp}?";
  }
| '{' fields::Params '}'
  {
    te.ast = abs:structureTypeExpr(fields.fieldAst, location=te.location);
    te.pp = pp"{${fields.pp}";
  }
| '(' params::TypeExprs ')' '->' ret::TypeExpr
  {
    te.ast = abs:functionTypeExpr(params.ast, ret.ast, location=te.location);
    te.pp = pp"(${params.pp}) -> ${ret.pp}";
  }
| n::Id_t
  {
    te.ast = abs:nameTypeExpr(abs:name(n.lexeme, location=n.location), location=te.location);
    te.pp = text(n.lexeme);
  }
| te1::TypeExpr '<' tes::TypeExprs '>'
  {
    te.ast = abs:genericAppTypeExpr(te1.ast, tes.ast, location=te.location);
    te.pp = pp"${te1.pp}<${tes.pp}>";
  }
| '[' te1::TypeExpr ']'
  {
    te.ast = te1.ast;
    te.pp = pp"[${te1.pp}]";
  }

closed nonterminal TypeExprs with ast<[abs:TypeExpr]>, pp;

concrete productions tes::TypeExprs
| h::TypeExpr ',' t::TypeExprs
  {
    tes.ast = h.ast :: t.ast;
    tes.pp = concat([h.pp, text(","), t.pp]);
  }
| h::TypeExpr
  {
    tes.ast = [h.ast];
    tes.pp = h.pp;
  }
|
  {
    tes.ast = [];
    tes.pp = text("");
  }

synthesized attribute astOrAny::abs:TypeExpr;
closed nonterminal MaybeTypeExpr with ast<abs:MaybeTypeExpr>, astOrAny, pp, location;

concrete productions mte::MaybeTypeExpr
| ':' h::TypeExpr
  {
    mte.ast = abs:justTypeExpr(h.ast, location=h.location);
    mte.astOrAny = h.ast;
    mte.pp = cat(text(":"), h.pp);
  }
|
  {
    mte.ast = abs:nothingTypeExpr(location=mte.location);
    mte.astOrAny = abs:anyTypeExpr(location=mte.location);
    mte.pp = text("");
  }