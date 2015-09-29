grammar gia:concretesyntax;

closed nonterminal TypeExpr with ast<abs:TypeExpr>, pp, location;

concrete production anyTypeExpr
te::TypeExpr ::= 'any'
{
  te.ast = abs:anyTypeExpr(location=te.location);
  te.pp = text("any");
}

concrete production intTypeExpr
te::TypeExpr ::= 'int'
{
  te.ast = abs:intTypeExpr(location=te.location);
  te.pp = text("int");
}

concrete production strTypeExpr
te::TypeExpr ::= 'str'
{
  te.ast = abs:strTypeExpr(location=te.location);
  te.pp = text("str");
}

concrete production listTypeExpr
te::TypeExpr ::= te1::TypeExpr '*'
{
  te.ast = abs:listTypeExpr(te1.ast, location=te.location);
  te.pp = pp"${te1.pp}*";
}

concrete production structureTypeExpr
te::TypeExpr ::= '{' fields::Fields '}'
{
  te.ast = abs:structureTypeExpr(fields.ast, location=te.location);
  te.pp = pp"{${fields.pp}";
}

concrete production functionTypeExpr
te::TypeExpr ::= '(' params::TypeExprs ')' '->' ret::TypeExpr
{
  te.ast = abs:functionTypeExpr(params.ast, ret.ast, location=te.location);
  te.pp = pp"(${params.pp}) -> ${ret.pp}";
}

concrete production nameTypeExpr
te::TypeExpr ::= n::Id_t
{
  te.ast = abs:nameTypeExpr(abs:name(n.lexeme, location=n.location), location=te.location);
  te.pp = text(n.lexeme);
}

closed nonterminal Fields with ast<[Pair<String abs:TypeExpr>]>, pp;

concrete productions fs::Fields
| n::Id_t ':' h::TypeExpr ',' t::Fields
  {
    fs.ast = pair(n.lexeme, h.ast) :: t.ast;
    fs.pp = concat([h.pp, text(","), t.pp]);
  }
| n::Id_t ':' h::TypeExpr
  {
    fs.ast = [pair(n.lexeme, h.ast)];
    fs.pp = h.pp;
  }
|
  {
    fs.ast = [];
    fs.pp = text("");
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

closed nonterminal MaybeTypeExpr with ast<abs:MaybeTypeExpr>, pp, location;

concrete productions mte::MaybeTypeExpr
| ':' h::TypeExpr
  {
    mte.ast = abs:justTypeExpr(h.ast, location=h.location);
    mte.pp = h.pp;
  }
|
  {
    mte.ast = abs:nothingTypeExpr(location=mte.location);
    mte.pp = text("");
  }