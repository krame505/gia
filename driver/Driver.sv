grammar gia:driver;

imports gia:concretesyntax as cnc;
imports gia:abstractsyntax as abs;

imports silver:langutil;
imports silver:langutil:pp;

function driver
IOVal<Integer> ::= args::[String] ioIn::IO parse::(ParseResult<cnc:Root>::=String String) exprParse::(ParseResult<cnc:Expr>::=String String)
{
  local result::ParseResult<cnc:Root> = parse(head(args), head(tail(args)));
  local exprResult::ParseResult<cnc:Expr> = exprParse(head(tail(tail(args))), "");
  local cst::Decorated cnc:Root = 
    decorate result.parseTree
    with {cnc:ioIn = ioIn;
          cnc:currentDir = "."; --TODO?
          cnc:parse = parse;};
  local expr::abs:Expr = exprResult.parseTree.ast;
  local ast::Decorated abs:Root =
    decorate cst.ast
    with {abs:evalExpr=expr;};

  return
    if null(args) || null(tail(args)) || null(tail(tail(args)))
    then ioval(print("Error: missing arguments\nThis jar should not be run manually, only called via the gia script", ioIn), 3)
    else if !result.parseSuccess
    then ioval(print(result.parseErrors ++ "\n", cst.cnc:ioOut), 2)
    else if !null(ast.errors)
    then ioval(print(messagesToString(ast.errors) ++ "\n", cst.cnc:ioOut), if containsErrors(ast.errors, false) then 1 else 0)
    else ioval(print(show(80, ast.abs:evalRes.pp) ++ "\n", cst.cnc:ioOut), 0);
}