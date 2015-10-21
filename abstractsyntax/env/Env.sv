grammar gia:abstractsyntax:env;

imports gia:abstractsyntax;

imports silver:util:raw:treemap as tm;

type Env<a> = tm:Map<String a>;
type Def<a> = Pair<String a>;

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

function addBackEnv
Env<a> ::= d::[Def<a>] e::Env<a>
{
  return tm:add(tm:toList(e) ++ d, emptyEnv());
}

function lookup
[a] ::= n::String e::Env<a>
{
  return tm:lookup(n, e);
}

function lookupList
Maybe<a> ::= n::String e::[Pair<String a>]
{
  return
    case e of
      [] -> nothing()
    | pair(n1, h) :: t ->
      if n == n1
      then just(h)
      else lookupList(n, t)
    end;
}