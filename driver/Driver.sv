grammar gia:driver;

imports gia:concretesyntax as cnc;
imports gia:abstractsyntax as abs;

imports silver:langutil;
imports silver:langutil:pp;

function driver
IOVal<Integer> ::= args::[String] ioIn::IO parse::(ParseResult<cnc:Root>::=String String) exprParse::(ParseResult<cnc:Expr>::=String String)
{
  local result::ParseResult<cnc:Root> = parse(head(args), head(tail(args)));
  local exprResult::ParseResult<cnc:Expr> = exprParse(implode(" ", tail(tail(args))), "");
  local cst::cnc:Root = result.parseTree;
  cst.cnc:ioIn = ioIn;
  cst.cnc:currentDir = "."; --TODO?
  cst.cnc:parse = parse;
  local expr::abs:Expr = exprResult.parseTree.ast;
  local ast::abs:Root = cst.ast;
  ast.abs:evalExpr = expr;

  return
    if null(args) || null(tail(args)) || null(tail(tail(args)))
    then ioval(print("Error: missing arguments\nThis jar should not be run manually, only called via the gia script", ioIn), 6)
    else if !result.parseSuccess
    then ioval(print(result.parseErrors ++ "\n", cst.cnc:ioOut), 5)
    else if !exprResult.parseSuccess
    then ioval(print(exprResult.parseErrors ++ "\n", cst.cnc:ioOut), 4)
    else if !null(ast.errors)
    then ioval(print(messagesToString(ast.errors) ++ "\n", cst.cnc:ioOut), if containsErrors(ast.errors, false) then 3 else 0)
    else if !null(ast.errors)
    then ioval(print(messagesToString(ast.abs:evalErrors) ++ "\n", cst.cnc:ioOut), if containsErrors(ast.abs:evalErrors, false) then 2 else 0)
    else case ast.abs:evalRes of
      abs:errorValue(_) -> ioval(print("Runtime errors:\n" ++ show(80, ast.abs:evalRes.abs:pp) ++ "\n", cst.cnc:ioOut), 1)
    | _ -> ioval(print(show(80, ast.abs:evalRes.abs:pp) ++ " : " ++ show(80, ast.abs:evalResType.abs:pp) ++ "\n", cst.cnc:ioOut), 0)
    end;
}