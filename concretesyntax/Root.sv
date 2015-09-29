grammar gia:concretesyntax;

imports gia:abstractsyntax as abs;

imports silver:langutil;
imports silver:langutil:pp;

-- Needed for 'use' statments
autocopy attribute currentDir::String;
autocopy attribute parse::(ParseResult<Root> ::= String String);
inherited attribute ioIn::IO;
synthesized attribute ioOut::IO;

closed nonterminal Root with ast<abs:Root>, ioIn, ioOut, currentDir, parse;

concrete production root
r::Root ::= d::Decls
{
  r.ast = abs:root(d.ast);
  d.ioIn = r.ioIn;
  r.ioOut = d.ioOut;
}