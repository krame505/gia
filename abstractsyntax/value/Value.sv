grammar gia:abstractsyntax:value;

imports gia:abstractsyntax;
imports gia:abstractsyntax:env;

imports silver:langutil hiding pp;
imports silver:langutil:pp with implode as ppImplode;
imports silver:util:raw:treeset as ts;

type ValueEnv = Env<Value>;
type ValueDef = Def<Value>;

autocopy attribute env::ValueEnv;
synthesized attribute defs::[ValueDef];

synthesized attribute index::(Value ::= Value Location);
synthesized attribute add::(Value ::= Value Location);
synthesized attribute sub::(Value ::= Value Location);
synthesized attribute mul::(Value ::= Value Location);
synthesized attribute div::(Value ::= Value Location);
synthesized attribute eq::(Value ::= Value Location);
synthesized attribute gt::(Value ::= Value Location);
synthesized attribute and::(Value ::= Value Location);
synthesized attribute or::(Value ::= Value Location);
synthesized attribute not::(Value ::= Location);
synthesized attribute cond::(Value ::= Location);
synthesized attribute access::(Value ::= Name Location);

nonterminal Value with pp, type, index, add, sub, mul, div, eq, gt, and, or, not, cond, access;

aspect default production
v::Value ::= 
{
  v.type = anyType();
  v.index = opError("[]", v, _, _);
  v.add = opError("+", v, _, _);
  v.sub = opError("-", v, _, _);
  v.mul = opError("*", v, _, _);
  v.div = opError("/", v, _, _);
  v.eq = opError("==", v, _, _);
  v.gt = opError(">", v, _, _);
  v.and = opError("&", v, _, _);
  v.or = opError("|", v, _, _);
  v.not = unaryOpError("!", v, _);
  v.cond = unaryOpError("if", v, _);
  v.access = accessDefault(v, _, _);
}

abstract production trueValue
v::Value ::= 
{
  v.pp = text("true");
  v.type = boolType();
  v.eq = eqTrue(_, _);
  v.and = andBool(v, _, _);
  v.or = orBool(v, _, _);
  v.not = unaryIdentity(falseValue(), _);
  v.cond = unaryIdentity(v, _);
}

abstract production falseValue
v::Value ::= 
{
  v.pp = text("false");
  v.type = boolType();
  v.eq = eqFalse(_, _);
  v.and = andBool(v, _, _);
  v.or = orBool(v, _, _);
  v.not = unaryIdentity(trueValue(), _);
  v.cond = unaryIdentity(v, _);
}

abstract production intValue
v::Value ::= i::Integer
{
  v.pp = text(toString(i));
  v.type = intType();
  v.add = addInt(i, _, _);
  v.sub = subInt(i, _, _);
  v.mul = mulInt(i, _, _);
  v.div = divInt(i, _, _);
  v.eq = eqInt(i, _, _);
  v.gt = gtInt(i, _, _);
  v.cond = unaryIdentity(if i == 0 then falseValue() else trueValue(), _);
}

abstract production strValue
v::Value ::= s::String
{
  v.pp = text("\"" ++ s ++ "\"");
  v.access = accessStr(s, _, _);
  v.type = strType();
  v.index = indexStr(s, _, _);
  v.add = catStr(s, _, _);
  v.mul = repeatStr(s, _, _);
  v.eq = eqStr(s, _, _);
}

abstract production listValue
v::Value ::= contents::[Value]
{
  v.pp = pp"[${ppImplode(text(", "), map((.pp), contents))}]";
  v.type = listType(foldr(mergeTypesOrDynamic, anyType(), map((.type), contents)));
  v.access = accessList(contents, _, _);
  v.index = indexList(contents, _, _);
  v.add = catList(contents, _, _);
  v.eq = eqList(contents, _, _);
  v.cond = unaryIdentity(if null(contents) then falseValue() else trueValue(), _);
}

-- TODO: Impliment more efficiently
abstract production setValue
v::Value ::= contents::[Value]
{
  v.pp = pp"{${ppImplode(text(", "), map((.pp), contents))}}";
  v.type = setType(foldr(mergeTypesOrDynamic, anyType(), map((.type), contents)));
  v.access = accessSet(contents, _, _);
  v.index = indexSet(contents, _, _);
--  v.add = unionSet(contents, _, _);
  v.sub = removeSet(contents, _, _);
  v.and = intersectSet(contents, _, _);
  v.or = unionSet(contents, _, _);
  v.eq = eqSet(contents, _, _);
  v.cond = unaryIdentity(if null(contents) then falseValue() else trueValue(), _);
}

abstract production functionValue
v::Value ::= name::String env::ValueEnv params::[Type] ret::Type paramNames::[String] body::Expr
{
  v.pp = pp"function ${text(name)}(${ppImplode(text(", "), map((.pp), params))})";
  v.type = functionType(params, ret);
}

abstract production nodeValue
v::Value ::= name::String type::Either<Type Name> children::[Value] bindings::[Pair<String Value>]
{
  v.pp = pp"${text(name)}(${ppImplode(text(", "), map((.pp), children))})";
  v.type =
    case type of
      left(t) -> t
    | right(n) -> dataType(n, zipWith(pair, map(fst, bindings), map((.type), map(snd, bindings))))
    end;
  v.access = accessNode(name, type, children, bindings, _, _);
  v.eq = eqNode(name, children, bindings, _, _);
  v.add = nodeOp("add", bindings, _, _);
  v.sub = nodeOp("sub", bindings, _, _);
  v.mul = nodeOp("mul", bindings, _, _);
  v.div = nodeOp("div", bindings, _, _);
  v.gt = nodeOp("gt", bindings, _, _);
  v.and = nodeOp("and", bindings, _, _);
  v.or = nodeOp("or", bindings, _, _);
  v.not = unaryNodeOp("not", bindings, _);
  v.cond = unaryNodeOp("cond", bindings, _);
}

abstract production structureValue
v::Value ::= bindings::[Pair<String Value>]
{
  v.pp =
    if null(bindings)
    then text("{}")
    else pp"{${ppImplode(text("; "), map((bindingPP), bindings))};}";
  v.type = structureType(zipWith(pair, map(fst, bindings), map((.type), map(snd, bindings))));
  v.access = access(bindings, _, _);
  v.eq = eqStructure(bindings, _, _);
  v.add = nodeOp("add", bindings, _, _);
  v.sub = nodeOp("sub", bindings, _, _);
  v.mul = nodeOp("mul", bindings, _, _);
  v.div = nodeOp("div", bindings, _, _);
  v.gt = nodeOp("gt", bindings, _, _);
  v.and = nodeOp("and", bindings, _, _);
  v.or = nodeOp("or", bindings, _, _);
  v.not = unaryNodeOp("not", bindings, _);
  v.cond = unaryNodeOp("cond", bindings, _);
}

function bindingPP
Document ::= b::Pair<String Value>
{
  return pp"${text(b.fst)} = ${b.snd.pp}";
}

abstract production lazyValue
v::Value ::= env::ValueEnv typeNameEnv::TypeEnv expr::Expr
{
  {-v.pp =
    if length(show(80, expr.pp)) > 10
    then pp"<lazy ...>"
    else pp"<lazy ${expr.pp}>";-}
  expr.env = env;
  expr.typeEnv = emptyEnv(); --TODO: Find bad dependency, temporary hack to avoid crashing
  expr.typeNameEnv = typeNameEnv; -- Needed for run-time type checking
  forwards to expr.value;
}

abstract production errorValue
v::Value ::= msgs::[Message]
{
  v.pp = text(implode("\n", map((.output), msgs)));
  v.eq = binaryIdentity(v, _, _);
}

function unaryIdentity
Value ::= v::Value loc::Location
{
  return v;
}

function binaryIdentity
Value ::= v1::Value v2::Value loc::Location
{
  return v1;
}

function eqTrue
Value ::= v::Value loc::Location
{
  return
    case v of
      falseValue() -> falseValue()
    | trueValue() -> trueValue()
    | _ -> opError("==", trueValue(), v, loc)
    end;
}

function eqFalse
Value ::= v::Value loc::Location
{
  return
    case v of
      falseValue() -> trueValue()
    | trueValue() -> falseValue()
    | _ -> opError("==", falseValue(), v, loc)
    end;
}

function andBool
Value ::= v1::Value v2::Value loc::Location
{
  return
    case v1, v2 of
      falseValue(), _ -> falseValue()
    | trueValue(), falseValue() -> falseValue()
    | trueValue(), trueValue() -> trueValue()
    | _, _ -> opError("==", v1, v2, loc)
    end;
}

function orBool
Value ::= v1::Value v2::Value loc::Location
{
  return
    case v1, v2 of
      trueValue(), _ -> trueValue()
    | falseValue(), trueValue() -> trueValue()
    | falseValue(), falseValue() -> falseValue()
    | _, _ -> opError("==", v1, v2, loc)
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
      intValue(j) -> if i == j then trueValue() else falseValue()
    | _ -> opError("==", intValue(i), v, loc)
    end;
}

function gtInt
Value ::= i::Integer v::Value loc::Location
{
  return
    case v of
      intValue(j) -> if i > j then trueValue() else falseValue()
    | _ -> opError(">", intValue(i), v, loc)
    end;
}

function accessStr
Value ::= s::String field::Name loc::Location
{
  return
    case field.name of
      "len" -> intValue(length(s))
    | _ -> accessDefault(strValue(s), field, loc)
    end;
}

function indexStr
Value ::= s::String v::Value loc::Location
{
  return
    case v of
      intValue(i) ->
        if i >= length(s)
        then errorValue([err(loc, s"String index out of bounds: ${toString(i)}")])
        else strValue(substring(i, i + 1, s))
    | _ -> opError("[]", strValue(s), v, loc)
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
        if j > 0
        then case repeatStr(s, intValue(j - 1), loc) of
            strValue(s1) -> strValue(s ++ s1)
          end
        else strValue("")
    | _ -> opError("+", strValue(s), v, loc)
    end;
}

function eqStr
Value ::= s::String v::Value loc::Location
{
  return
    case v of
      strValue(t) -> if s == t then trueValue() else falseValue()
    | _ -> opError("==", strValue(s), v, loc)
    end;
}

function accessList
Value ::= l::[Value] field::Name loc::Location
{
  return
    case field.name of
      "len" -> intValue(length(l))
    | _ -> accessDefault(listValue(l), field, loc)
    end;
}

function indexList
Value ::= l::[Value] v::Value loc::Location
{
  return
    case v of
      intValue(i) ->
        if i >= length(l)
        then errorValue([err(loc, s"List index out of bounds: ${toString(i)}")])
        else head(drop(i, l))
    | _ -> opError("[]", listValue(l), v, loc)
    end;
}

function catList
Value ::= l::[Value] v::Value loc::Location
{
  return
    case v of
      listValue(m) -> listValue(l ++ m)
    | _ -> opError("+", listValue(l), v, loc)
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
      w :: t1, listValue(x :: t2) -> andBool(w.eq(x, loc), eqList(t1, listValue(t2), loc), loc)
    | [], listValue([]) -> trueValue()
    | _, listValue([]) -> falseValue()
    | [], listValue(_) -> falseValue()
    | _, _ -> opError("==", listValue(l), v, loc)
    end;
}

function accessSet
Value ::= l::[Value] field::Name loc::Location
{
  return
    case field.name of
      "len" -> intValue(length(l))
    | _ -> accessDefault(setValue(l), field, loc)
    end;
}

function indexSet
Value ::= s::[Value] v::Value loc::Location
{
  local lookup::[Value] = filter(eqValue(_, v), s);
  return
    if null(lookup)
    then constructNone()
    else constructSome(head(lookup));
}

function intersectSet
Value ::= s::[Value] v::Value loc::Location
{
  return
    case v of
      setValue(s1) -> setValue(intersectBy(eqValue, s, s1))
    | _ -> opError("|", setValue(s), v, loc)
    end;
}

function unionSet
Value ::= s::[Value] v::Value loc::Location
{
  return
    case v of
      setValue(s1) -> setValue(unionBy(eqValue, s, s1))
    | _ -> opError("&", setValue(s), v, loc)
    end;
}

function removeSet
Value ::= s::[Value] v::Value loc::Location
{
  return
    case v of
      setValue(s1) -> setValue(removeAllBy(eqValue, s, s1))
    | _ -> opError("-", setValue(s), v, loc)
    end;
}

function eqSet
Value ::= s::[Value] v::Value loc::Location
{
  return
    case v of
      setValue(s1) ->
        if foldr(andHelper, true, map(containsBy(eqValue, _, s), s1)) &&
           foldr(andHelper, true, map(containsBy(eqValue, _, s1), s))
        then trueValue()
        else falseValue()
    | _ -> opError("==", setValue(s), v, loc)
    end;
}

-- Seems like something like this should be built-in
function andHelper
Boolean ::= b1::Boolean b2::Boolean
{
  return b1 && b2;
}

function accessDefault
Value ::= v::Value field::Name loc::Location
{
  return
    case field.name of
      "toStr" -> strValue(show(80, v.pp))
    | "pp" -> strValue(show(80, v.pp))
    | "internal_debug_hackUnparse" -> strValue(hackUnparse(v))
    | _ -> nameOpError(".", v, field, loc)
    end;
}

function access
Value ::= bindings::[Pair<String Value>] field::Name loc::Location
{
  return accessHelp(bindings, bindings, field, loc);
}

function accessHelp
Value ::= bindings::[Pair<String Value>] oldBindings::[Pair<String Value>] field::Name loc::Location
{
  return
    case bindings of
      pair(s, v) :: rest -> 
        if s == field.name
        then v
        else accessHelp(rest, oldBindings, field, loc)
    | [] -> accessDefault(structureValue(oldBindings), field, loc)
    end;
}

function accessNode
Value ::= name::String type::Either<Type Name> children::[Value] bindings::[Pair<String Value>] field::Name loc::Location
{
  return accessNodeHelp(name, type, children, bindings, bindings, field, loc);
}

function accessNodeHelp
Value ::= name::String type::Either<Type Name> children::[Value] bindings::[Pair<String Value>] oldBindings::[Pair<String Value>] field::Name loc::Location
{
  return
    case bindings of
      pair(s, v) :: rest -> 
        if s == field.name
        then v
        else accessHelp(rest, oldBindings, field, loc)
    | [] -> accessDefault(nodeValue(name, type, children, oldBindings), field, loc)
    end;
}

function nodeOp
Value ::= op::String bindings::[Pair<String Value>] v::Value loc::Location
{
  local lookup::Value = access(bindings, name(op, location=bogusLocation), loc);
  local res::Expr = 
    app(
      valueExpr(lookup, location=bogusLocation),
      consExpr(valueExpr(v, location=bogusLocation), nilExpr()),
      location=bogusLocation);
  res.env = emptyEnv();
  res.typeEnv = error("Value shouldn't depend on typeEnv");
  res.typeNameEnv = error("Value shouldn't depend on typeNameEnv");
  return
    case v, lookup of
      errorValue(_), _ -> v
    | _, functionValue(_, _, _, _, _, _) -> res.value
    | _, _ -> lookup -- TODO: Better error message
    end;
}

function unaryNodeOp
Value ::= op::String bindings::[Pair<String Value>] loc::Location
{
  return access(bindings, name(op, location=bogusLocation), loc);
}

function eqNode
Value ::= n::String l::[Value] bindings::[Pair<String Value>] v::Value loc::Location
{
  local lookup::Value = access(bindings, name("eq", location=bogusLocation), loc);
  return
    case lookup, v of
      functionValue(_, _, _, _, _, _), _ -> nodeOp("eq", bindings, v, loc)
    | _, nodeValue(n1, _, l1, _) ->
      if n == n1
      then eqList(l, listValue(l1), loc)
      else falseValue()
    | _, structureValue(fields) ->
      if foldr(andHelper, true, zipWith(stringEq, map(fst, bindings), map(fst, fields)))
      then eqList(map(snd, bindings), listValue(map(snd, fields)), loc)
      else falseValue()
    | _, _ -> opError("==", nodeValue(n, right(name(n, location=bogusLocation)), l, []), v, loc)
    end;
}

function eqStructure
Value ::= bindings::[Pair<String Value>] v::Value loc::Location
{
  local lookup::Value = access(bindings, name("eq", location=bogusLocation), loc);
  return
    case lookup, v of
      functionValue(_, _, _, _, _, _), _ -> nodeOp("eq", bindings, v, loc)
    | _, nodeValue(_, _, _, fields) ->
      if foldr(andHelper, true, zipWith(stringEq, map(fst, bindings), map(fst, fields)))
      then eqList(map(snd, bindings), listValue(map(snd, fields)), loc)
      else falseValue()
    | _, structureValue(fields) ->
      if foldr(andHelper, true, zipWith(stringEq, map(fst, bindings), map(fst, fields)))
      then eqList(map(snd, bindings), listValue(map(snd, fields)), loc)
      else falseValue()
    | _, _ -> opError("==", structureValue(bindings), v, loc)
    end;
}

function nameOpError
Value ::= op::String v::Value n::Name loc::Location
{
  return
    case v of
      errorValue(_) -> v
    | _ -> errorValue([err(loc, s"${op} undefined for ${show(80, v.type.pp)} and ${n.name}")])
    end;
}

function opError
Value ::= op::String v1::Value v2::Value loc::Location
{
  return
    case v1, v2 of
      errorValue(_), _ -> v1
    | _, errorValue(_) -> v2
    | _, _ -> errorValue([err(loc, s"${op} undefined for ${show(80, v1.type.pp)} and ${show(80, v2.type.pp)}")])
    end;
}

function unaryOpError
Value ::= op::String v::Value loc::Location
{
  return
    case v of
      errorValue(_) -> v
    | _ -> errorValue([err(loc, s"${op} undefined for ${show(80, v.type.pp)}")])
    end;
}

-- Util
function constructSome
Value ::= v::Value
{
  return
    nodeValue(
      "Some",
      right(name("Maybe", location=bogusLocation)),
      [v],
      [pair("hasValue", trueValue()),
       pair("value", v)]);
}

function constructNone
Value ::= 
{
  return
    nodeValue(
      "None",
      right(name("Maybe", location=bogusLocation)),
      [],
      [pair("hasValue", falseValue()),
       pair("value", errorValue([err(bogusLocation, "Demanded value from None")]))]);
}

function eqValue
Boolean ::= v1::Value v2::Value
{
  return
    case v1.eq(v2, bogusLocation) of
      trueValue() -> true
    | _ -> false
    end;
}

function emptySet
Value ::= 
{
  return setValue([]);
}