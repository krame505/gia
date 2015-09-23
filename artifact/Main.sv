grammar gia:artifact;

imports gia:concretesyntax as cnc;

import gia:driver;

parser parse::cnc:Root {
  gia:concretesyntax;
}

parser exprParse::cnc:Expr {
  gia:concretesyntax;
}

function main
IOVal<Integer> ::= args::[String] io_in::IO
{
  return driver(args, io_in, parse, exprParse);
}
