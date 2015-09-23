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
  
  local file::String = substring(1, length(s.lexeme) - 2, s.lexeme);
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
  local text::IOVal<String> = readFile(fileWithPath, text.io);
  local parseResult::ParseResult<Root> = d.parse(text.iovalue, file);
  local cst::Decorated Decls =
    decorate 
      if !isF.iovalue
      then parseErrorDecls("File " ++ fileWithPath ++ " not found")
      else if parseResult.parseSuccess
      then case parseResult.parseTree of root(ds) -> ds end
      else parseErrorDecls(parseResult.parseErrors)
    with {ioIn = if !isF.iovalue then isF.io else text.io;
          currentDir = newDir;
          parse = d.parse;};
}

concrete production nodeDecl
d::Decl ::= n::Id_t p::Params b::Body
{
  d.ast = abs:nodeDecl(abs:name(n.lexeme, location=n.location), p.ast, b.ast, location=d.location);
  d.ioOut = d.ioIn;
}

{-
concrete production FunctionDecl
d::Decl ::= n::Id_t p::Params e::Expr
{
  d.ast = ...;
}
-}

nonterminal Params with ast<abs:Params>, location;

concrete production consParam
p::Params ::= h::Id_t t::Params
{
  p.ast = abs:consParam(abs:name(h.lexeme, location=h.location), t.ast, location=p.location);
}

concrete production nilParam
p::Params ::= 
{
  p.ast = abs:nilParam(location=p.location);
}