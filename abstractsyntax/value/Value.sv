grammar gia:abstractsyntax:value;

imports gia:abstractsyntax;
imports gia:abstractsyntax:env;

imports silver:langutil hiding pp;
imports silver:langutil:pp with implode as ppImplode;

synthesized attribute add::(Value ::= Value Location);
synthesized attribute and::(Value ::= Value Location);
synthesized attribute or::(Value ::= Value Location);
synthesized attribute access::(Value ::= Name Location);

nonterminal Value with pp, add, and, or, access;

aspect default production
v::Value ::= 
{
  v.add = opError("+", v, _, _);
  v.and = and(v, _, _); -- a & b = a iff b != none
  v.or = identity(v, _, _); -- a | b = a iff a != none
  v.access = nameOpError(".", v, _, _);
}

abstract production noneValue
v::Value ::= 
{
  v.pp = text("none");
  v.and = identity(v, _, _);
  v.or = identity(_, v, _);
}

abstract production intValue
v::Value ::= i::Integer
{
  v.pp = text(toString(i));
  v.add = addInt(i, _, _);
}

abstract production strValue
v::Value ::= s::String
{
  v.pp = text("\"" ++ s ++ "\"");
  v.add = addStr(s, _, _);
}

abstract production functionValue
v::Value ::= env::Env params::Params body::Expr
{
  local id::Integer = genInt();
  v.pp = pp"<function ${text(toString(id))}>(${params.pp})";
}

abstract production constructorValue
v::Value ::= env::Env params::Params rules::[Pair<String Expr>]
{
  local id::Integer = genInt();
  v.pp = pp"<constructor ${text(toString(id))}>(${params.pp})";
}

abstract production nodeValue
v::Value ::= name::String children::[Value] bindings::[Pair<String Value>]
{
  v.pp = pp"${text(name)}(${ppImplode(text(", "), map((.pp), children))})";
  v.access = access(bindings, _, _);
}

abstract production listValue
v::Value ::= contents::[Value]
{
  v.pp = pp"[${ppImplode(text(", "), map((.pp), contents))}]";
  v.add = addList(contents, _, _);
}

abstract production errorValue
v::Value ::= msgs::[Message]
{
  v.pp = text(implode("\n", map((.message), msgs)));
}

function identity
Value ::= v1::Value v2::Value loc::Location
{
  return v1;
}

function and
Value ::= v1::Value v2::Value loc::Location
{
  return
    case v1, v2 of
      noneValue(), _ -> noneValue()
    | _, noneValue() -> noneValue()
    | _, _ -> v1
    end;
}

function addInt
Value ::= i::Integer v::Value loc::Location
{
  return
    case v of
      intValue(j) -> intValue(i + j)
    | strValue(s) -> strValue(toString(i) ++ s)
    | _ -> opError("+", intValue(i), v, loc)
    end;
}

function addStr
Value ::= s::String v::Value loc::Location
{
  return
    case v of
      intValue(j) -> strValue(s ++ toString(j))
    | strValue(t) -> strValue(s ++ t)
    | _ -> opError("+", strValue(s), v, loc)
    end;
}

function addList
Value ::= l::[Value] v::Value loc::Location
{
  return
    case l, v of
      _, listValue(m) -> listValue(l ++ m)
    | w :: [], _ -> w.add(v, loc)
    | _, _ -> opError("+", listValue(l), v, loc)
    end;
}

function access
Value ::= bindings::[Pair<String Value>] field::Name loc::Location
{
  return
    case bindings of
      pair(s, v) :: rest -> 
        if s == field.name
        then v
        else access(rest, field, loc)
    | [] -> errorValue([err(loc, s"Value does not have field ${field.name}")])
    end;
}

function nameOpError
Value ::= op::String v::Value n::Name loc::Location
{
  return
    case v of
      errorValue(_) -> v
    | _ -> errorValue([err(loc, s"${op} undefined for ${show(80, v.pp)} and ${n.name}")])
    end;
}

function opError
Value ::= op::String v1::Value v2::Value loc::Location
{
  return
    case v1, v2 of
      errorValue(_), _ -> v1
    | _, errorValue(_) -> v2
    | _, _ -> errorValue([err(loc, s"${op} undefined for ${show(80, v1.pp)} and ${show(80, v2.pp)}")])
    end;
}