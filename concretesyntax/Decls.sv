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

concrete production valDecl
d::Decl ::= n::Id_t '=' e::Expr ';'
{
  d.ast = abs:valDecl(abs:name(n.lexeme, location=n.location), e.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production typeDecl
d::Decl ::= 'type' n::Id_t '=' te::TypeExpr ';'
{
  d.ast = abs:typeDecl(abs:name(n.lexeme, location=n.location), te.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production dataTypeDecl
d::Decl ::= 'datatype' n::Id_t '=' te::TypeExpr ';'
{
  d.ast = abs:dataTypeDecl(abs:name(n.lexeme, location=n.location), te.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production nodeDecl
d::Decl ::= n::Id_t '(' p::Params ')' mte::MaybeTypeExpr '{' b::Body '}'
{
  d.ast = abs:nodeDecl(abs:name(n.lexeme, location=n.location), p.ast, mte.ast, b.ast, location=d.location);
  d.ioOut = d.ioIn;
}

concrete production nodeDeclNoBody
d::Decl ::= n::Id_t '(' p::Params ')' mte::MaybeTypeExpr b::';'
{
  d.ast = abs:nodeDecl(abs:name(n.lexeme, location=n.location), p.ast, mte.ast, abs:nilBody(location=b.location), location=d.location);
  d.ioOut = d.ioIn;
}

closed nonterminal Params with ast<abs:Params>, location;

concrete productions p::Params
| h::Id_t  mte::MaybeTypeExpr',' t::Params
  {
    p.ast = abs:consParam(abs:name(h.lexeme, location=h.location), mte.ast, t.ast);
  }
| h::Id_t mte::MaybeTypeExpr
  {
    p.ast = abs:consParam(abs:name(h.lexeme, location=h.location), mte.ast, abs:nilParam());
  }
|
  {
    p.ast = abs:nilParam();
  }