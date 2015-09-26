grammar gia:abstractsyntax;

imports gia:abstractsyntax:value as val;
imports gia:abstractsyntax:env;

exports gia:abstractsyntax:value;

imports silver:langutil;
imports silver:langutil:pp;

synthesized attribute pp::Document; -- Why do we have to re-define this?

autocopy attribute evalExpr::Expr;
synthesized attribute evalRes::val:Value;
synthesized attribute evalErrors::[Message];

nonterminal Root with errors, evalExpr, evalRes, evalErrors;

abstract production root
r::Root ::= d::Decls
{
  r.errors := d.errors;
  d.evalExpr = r.evalExpr;
  r.evalRes = d.evalRes;
  r.evalErrors = d.evalErrors;
  
  d.env = emptyEnv();
}

-- Don't know where to put this...
global bogusLocation :: Location = loc("<generated>", -1,-1,-1,-1,-1,-1);