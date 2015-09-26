grammar gia:abstractsyntax:env;

imports gia:abstractsyntax;

imports silver:util:raw:treemap as tm;

type Env = tm:Map<String Value>;
type Def = Pair<String Value>;

autocopy attribute env::Env;
synthesized attribute defs::[Def];
{-
nonterminal EnvItem with value;

abstract production valueItem
ei::EnvItem ::= v::Value
{
  ei.value = v;
}
-}
function emptyEnv
Env ::=
{
  return tm:empty(compareString);
}

function addEnv
Env ::= d::[Def] e::Env
{
  return tm:add(d, e);
}

function lookup
[Value] ::= n::String e::Env
{
  return tm:lookup(n, e);
}