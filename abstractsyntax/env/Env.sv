grammar gia:abstractsyntax:env;

imports gia:abstractsyntax;

imports silver:util:raw:treemap as tm;

type Env<a> = tm:Map<String a>;
type Def<a> = Pair<String a>;

type ValueEnv = Env<Value>;
type ValueDef = Def<Value>;

--type TypeEnv = Env<Type>;
--type TypeDef = Def<Type>;

autocopy attribute env::ValueEnv;
synthesized attribute defs::[ValueDef];

--autocopy attribute typeEnv::TypeEnv;
--synthesized attribute typeDefs::[TypeDef];
{-
nonterminal EnvItem with value;

abstract production valueItem
ei::EnvItem ::= v::Value
{
  ei.value = v;
}
-}
function emptyEnv
Env<a> ::=
{
  return tm:empty(compareString);
}

function addEnv
Env<a> ::= d::[Def<a>] e::Env<a>
{
  return tm:add(d, e);
}

function lookup
[a] ::= n::String e::Env<a>
{
  return tm:lookup(n, e);
}