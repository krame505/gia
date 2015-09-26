grammar gia:abstractsyntax:value;

imports gia:abstractsyntax;
imports gia:abstractsyntax:env;

imports silver:langutil hiding pp;
imports silver:langutil:pp with implode as ppImplode;

synthesized attribute add::(Value ::= Value Location);
synthesized attribute sub::(Value ::= Value Location);
synthesized attribute mul::(Value ::= Value Location);
synthesized attribute div::(Value ::= Value Location);
synthesized attribute eq::(Value ::= Value Location);
synthesized attribute gt::(Value ::= Value Location);
synthesized attribute and::(Value ::= Value Location);
synthesized attribute or::(Value ::= Value Location);
synthesized attribute access::(Value ::= Name Location);

nonterminal Value with pp, add, sub, mul, div, eq, gt, and, or, access;

aspect default production
v::Value ::= 
{
  v.add = opError("+", v, _, _);
  v.sub = opError("-", v, _, _);
  v.mul = opError("*", v, _, _);
  v.div = opError("/", v, _, _);
  v.gt = opError(">", v, _, _);
  v.and = and(v, _, _); -- a & b = a iff b != none
  v.or = identity(v, _, _); -- a | b = a iff a != none
  v.access = nameOpError(".", v, _, _);
}

abstract production noneValue
v::Value ::= 
{
  v.pp = text("none");
  v.eq = eqNone(_, _);
  v.and = identity(v, _, _);
  v.or = identity(_, v, _);
}

abstract production intValue
v::Value ::= i::Integer
{
  v.pp = text(toString(i));
  v.add = addInt(i, _, _);
  v.sub = subInt(i, _, _);
  v.mul = mulInt(i, _, _);
  v.div = divInt(i, _, _);
  v.eq = eqInt(i, _, _);
  v.gt = gtInt(i, _, _);
}

abstract production strValue
v::Value ::= s::String
{
  v.pp = text("\"" ++ s ++ "\"");
  v.add = catStr(s, _, _);
  v.mul = repeatStr(s, _, _);
  v.eq = eqStr(s, _, _);
}

abstract production listValue
v::Value ::= contents::[Value]
{
  v.pp = pp"[${ppImplode(text(", "), map((.pp), contents))}]";
  v.add = catList(contents, _, _);
  v.eq = eqList(contents, _, _);
}

abstract production functionValue
v::Value ::= name::String env::Env params::Params body::Body
{
  v.pp = pp"function ${text(name)}(${params.pp})";
}

abstract production nodeValue
v::Value ::= name::String children::[Value] bindings::[Pair<String Value>]
{
  v.pp = pp"${text(name)}(${ppImplode(text(", "), map((.pp), children))})";
  v.access = access(bindings, _, _);
  v.eq = eqNode(name, children, _, _);
}

abstract production lazyValue
v::Value ::= env::Env expr::Expr
{
  expr.env = env;
  forwards to expr.value;
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

function eqNone
Value ::= v::Value loc::Location
{
  return
    case v of
      noneValue() -> intValue(1)
    | _ -> noneValue()
    end;
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

function subInt
Value ::= i::Integer v::Value loc::Location
{
  return
    case v of
      intValue(j) -> intValue(i - j)
    | _ -> opError("-", intValue(i), v, loc)
    end;
}

function mulInt
Value ::= i::Integer v::Value loc::Location
{
  return
    case v of
      intValue(j) -> intValue(i * j)
    | strValue(s) -> repeatStr(s, intValue(i), loc)
    | listValue(vs) -> repeatList(vs, intValue(i), loc)
    | _ -> opError("*", intValue(i), v, loc)
    end;
}

function divInt
Value ::= i::Integer v::Value loc::Location
{
  return
    case v of
      intValue(0) -> errorValue([err(loc, "Division by zero")])
    | intValue(j) -> intValue(i / j)
    | _ -> opError("/", intValue(i), v, loc)
    end;
}

function eqInt
Value ::= i::Integer v::Value loc::Location
{
  return
    case v of
      intValue(j) -> if i == j then intValue(1) else noneValue()
    | _ -> opError("==", intValue(i), v, loc)
    end;
}

function gtInt
Value ::= i::Integer v::Value loc::Location
{
  return
    case v of
      intValue(j) -> if i > j then intValue(1) else noneValue()
    | _ -> opError(">", intValue(i), v, loc)
    end;
}

function catStr
Value ::= s::String v::Value loc::Location
{
  return
    case v of
      intValue(j) -> strValue(s ++ toString(j))
    | strValue(t) -> strValue(s ++ t)
    | _ -> opError("+", strValue(s), v, loc)
    end;
}

function repeatStr
Value ::= s::String v::Value loc::Location
{
  return
    case v of
      intValue(j) ->
        case repeatStr(s, intValue(j - 1), loc) of
          strValue(s1) -> strValue(s ++ s1)
        end
    | _ -> opError("+", strValue(s), v, loc)
    end;
}

function eqStr
Value ::= s::String v::Value loc::Location
{
  return
    case v of
      strValue(t) -> if s == t then intValue(1) else noneValue()
    | _ -> opError("==", strValue(s), v, loc)
    end;
}

function catList
Value ::= l::[Value] v::Value loc::Location
{
  return
    case l, v of
      _, listValue(m) -> listValue(l ++ m)
    | w :: [], _ -> w.add(v, loc)
    | _, _ -> opError("+", listValue(l), v, loc)
    end;
}

function repeatList
Value ::= l::[Value] v::Value loc::Location
{
  return
    case v of
      intValue(j) ->
        case repeatList(l, intValue(j - 1), loc) of
          listValue(l1) -> listValue(l ++ l1)
        end
    | _ -> opError("+", listValue(l), v, loc)
    end;
}

function eqList
Value ::= l::[Value] v::Value loc::Location
{
  return
    case l, v of
      w :: t1, listValue(x :: t2) -> and(w.eq(x, loc), eqList(t1, listValue(t2), loc), loc)
    | [], listValue([]) -> intValue(1)
    | _, listValue([]) -> noneValue()
    | [], listValue(_) -> noneValue()
    | _, _ -> opError("==", listValue(l), v, loc)
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

function eqNode
Value ::= n::String l::[Value] v::Value loc::Location
{
  return
    case v of
      nodeValue(n1, l1, _) -> if n == n1 then eqList(l, v, loc) else noneValue()
    | _ -> opError("==", nodeValue(n, l, []), v, loc)
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