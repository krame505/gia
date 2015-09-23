grammar gia:abstractsyntax;

imports gia:abstractsyntax:value as val;
imports gia:abstractsyntax:env;

imports silver:langutil;
imports silver:langutil:pp;

autocopy attribute evalExpr::Expr;
synthesized attribute evalRes::val:Value;

nonterminal Root with errors, evalExpr, evalRes;

abstract production root
r::Root ::= d::Decls
{
  r.errors := d.errors;
  d.evalExpr = r.evalExpr;
  
  d.env = emptyEnv();
}

-- Don't know where to put this...
global bogusLocation :: Location = loc("<generated>", -1,-1,-1,-1,-1,-1);