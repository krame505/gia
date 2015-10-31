grammar gia:concretesyntax;

closed nonterminal Decls with ast<abs:Decls>, ioIn, ioOut, currentDir, parse;

concrete production consDecl
d::Decls ::= h::Decl t::Decls
{
  d.ast = abs:consDecl(h.ast, t.ast);
  h.ioIn = d.ioIn;
  t.ioIn = h.ioOut;
  d.ioOut = t.ioOut;
}
{-
concrete production oneDecl
d::Decls ::= h::Decl
{
  d.ast = abs:consDecl(h.ast, abs:nilDecl());
  h.ioIn = d.ioIn;
  d.ioOut = h.ioOut;
}
-}
concrete production returnDecl
d::Decls ::= 'return' e::Expr ';'
{
  d.ast = abs:returnDecl(e.ast);
  d.ioOut = d.ioIn;
}

concrete production nilDecl
d::Decls ::= 
{
  d.ast = abs:nilDecl();
  d.ioOut = d.ioIn;
}

abstract production parseErrorDecls
d::Decls ::= errorTxt::String
{
  d.ast = abs:parseErrorDecls(errorTxt);
  d.ioOut = d.ioIn;
}

closed nonterminal Decl with ast<abs:Decl>, ioIn, ioOut, currentDir, parse, location;

concrete production useDecl
d::Decl ::= 'use' s::StringConstant_t ';'
{
  d.ast = abs:decls(cst.ast, location=d.location);
  d.ioOut = cst.ioOut;
  
  local file::String = substring(1, length(s.lexeme) - 1, s.lexeme);
  local fileWithPath::String =
    if substring(0, 1, file) == "/"
    then file
    else d.currentDir ++ "/" ++ file;
  local filePathEndIndex::Integer = lastIndexOf("/", file);
  local newDir::String =
    d.currentDir ++
    if filePathEndIndex > 0
    then "/" ++ substring(0, filePathEndIndex, file)
    else "";
  local isF::IOVal<Boolean> = isFile(fileWithPath, d.ioIn);
  local text::IOVal<String> = readFile(fileWithPath, isF.io);
  local parseResult::ParseResult<Root> = d.parse(text.iovalue, file);
  local cst::Decls =
    if !isF.iovalue
    then parseErrorDecls("File " ++ fileWithPath ++ " not found")
    else if parseResult.parseSuccess
    then case parseResult.parseTree of root(ds) -> ds end
    else parseErrorDecls(parseResult.parseErrors);
  cst.ioIn = if !isF.iovalue then isF.io else text.io;
  cst.currentDir = newDir;
  cst.parse = d.parse;
}

concrete production openDecl
d::Decl ::= 'open' e::Expr ';'
{
  d.ast = abs:openDecl(e.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production valDecl
d::Decl ::= n::Id_t mte::MaybeTypeExpr '=' e::Expr ';'
{
  d.ast = abs:valDecl(abs:name(n.lexeme, location=n.location), mte.ast, e.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production typeDecl
d::Decl ::= 'type' n::Id_t mgp::MaybeGenericParams '=' te::TypeExpr ';'
{
  d.ast = abs:typeDecl(abs:name(n.lexeme, location=n.location), mgp.ast, te.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production dataTypeDecl
d::Decl ::= 'datatype' n::Id_t mgp::MaybeGenericParams me::MaybeExtends '=' te::TypeExpr ';'
{
  d.ast = abs:dataTypeDecl(abs:name(n.lexeme, location=n.location), mgp.ast, te.ast, me.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production nodeDecl
d::Decl ::= n::Id_t '(' p::Params ')' mte::MaybeTypeExpr b::Expr ';'
{
  d.ast = abs:nodeDecl(abs:name(n.lexeme, location=n.location), p.ast, mte.ast, b.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production nodeDeclNoBody
d::Decl ::= n::Id_t '(' p::Params ')' mte::MaybeTypeExpr b::';'
{
  d.ast =
    abs:nodeDecl(
      abs:name(n.lexeme, location=n.location),
      p.ast,
      mte.ast,
      abs:declExpr(abs:nilDecl(), location=b.location), location=d.location);
  d.ioOut = d.ioIn;
}

synthesized attribute fieldAst::[Pair<String abs:TypeExpr>];
closed nonterminal Params with ast<abs:Params>, fieldAst, pp, location;

concrete productions p::Params
| h::Id_t mte::MaybeTypeExpr ',' t::Params
  {
    p.ast = abs:consParam(abs:name(h.lexeme, location=h.location), mte.ast, t.ast);
    p.fieldAst = pair(h.lexeme, mte.astOrAny) :: t.fieldAst;
    p.pp = pp"${text(h.lexeme)}${mte.pp}, ${t.pp}";
  }
| h::Id_t mte::MaybeTypeExpr
  {
    p.ast = abs:consParam(abs:name(h.lexeme, location=h.location), mte.ast, abs:nilParam());
    p.fieldAst = [pair(h.lexeme, mte.astOrAny)];
    p.pp = cat(text(h.lexeme), mte.pp);
  }
|
  {
    p.ast = abs:nilParam();
    p.fieldAst = [];
    p.pp = text("");
  }

closed nonterminal MaybeGenericParams with ast<[abs:Name]>, pp, location;

concrete productions mgp::MaybeGenericParams
| '<' gp::GenericParams '>'
  {
    mgp.ast = gp.ast;
    mgp.pp = pp"<${gp.pp}>";
  }
|
  {
    mgp.ast = [];
    mgp.pp = text("");
  }

closed nonterminal GenericParams with ast<[abs:Name]>, pp;

concrete productions gp::GenericParams
| h::Id_t ',' t::GenericParams
  {
    gp.ast = abs:name(h.lexeme, location=h.location) :: t.ast;
    gp.pp = text(h.lexeme);
  }
| h::Id_t
  {
    gp.ast = [abs:name(h.lexeme, location=h.location)];
    gp.pp = text(h.lexeme);
  }
|
  {
    gp.ast = [];
    gp.pp = text("");
  }

closed nonterminal MaybeExtends with ast<abs:TypeExpr>, pp, location;

concrete productions me::MaybeExtends
| 'extends' n::Id_t
  {
    me.ast = abs:nameTypeExpr(abs:name(n.lexeme, location=n.location), location=n.location);
    me.pp = text(n.lexeme);
  }
|
  {
    me.ast = abs:anyTypeExpr(location=me.location);
    me.pp = text("");
  }