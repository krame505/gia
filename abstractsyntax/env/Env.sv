grammar gia:abstractsyntax:env;

imports gia:abstractsyntax;
imports gia:abstractsyntax:value;

imports silver:util:raw:treemap as tm;

type Env = tm:Map<String EnvItem>;
type Def = Pair<String EnvItem>;

autocopy attribute env::Env;
synthesized attribute defs::[Def];

nonterminal EnvItem with value;

abstract production valueItem
ei::EnvItem ::= v::Value
{
  ei.value = v;
}

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
[EnvItem] ::= n::String e::Env
{
  return tm:lookup(n, e);
}