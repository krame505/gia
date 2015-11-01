grammar gia:abstractsyntax;

synthesized attribute patternErrors::[Message] with ++;
synthesized attribute freeVars::[Name];
synthesized attribute value::val:Value;
inherited attribute matchValue::val:Value;
synthesized attribute matchRes::val:Value;

nonterminal Expr with val:env, errors, patternErrors, pp, freeVars, value, matchValue, matchRes, location;

aspect default production
e::Expr ::=
{
  e.patternErrors := [];
  e.matchRes = val:constructNone();
}

abstract production valueExpr
e::Expr ::= v::val:Value
{
  e.errors := [];
  e.pp = text("<value>");
  e.freeVars = [];
  e.value = v;
  e.matchRes = error("Matching on valueExpr");
}

abstract production errorExpr
e::Expr ::= e1::Expr
{
  e.errors := e1.errors;
  e.pp = pp"error(${e1.pp})";
  e.freeVars = e1.freeVars;
  e.value =
    case e1.value of
      val:strValue(s) -> val:errorValue([err(e.location, s)])
    | _ -> val:errorValue([err(e1.location, "Invalid type to error")])
    end;
  e.matchRes = error("Matching on valueExpr");
}

abstract production trueLiteral
e::Expr ::= 
{
  e.errors := [];
  e.pp = text("true");
  e.freeVars = [];
  e.value = val:trueValue();
  e.matchRes = 
    case e.matchValue of
      val:trueValue() ->  val:constructSome(val:listValue([]))
    | _ -> val:constructNone()
    end;
}

abstract production falseLiteral
e::Expr ::= 
{
  e.errors := [];
  e.pp = text("false");
  e.freeVars = [];
  e.value = val:falseValue();
  e.matchRes = 
    case e.matchValue of
      val:falseValue() ->  val:constructSome(val:listValue([]))
    | _ -> val:constructNone()
    end;
}

abstract production intLiteral
e::Expr ::= i::Integer
{
  e.errors := [];
  e.pp = text(toString(i));
  e.freeVars = [];
  e.value = val:intValue(i);
  e.matchRes =
    case e.matchValue of
      val:intValue(j) -> if i == j then val:constructSome(val:listValue([])) else val:constructNone()
    | _ -> val:constructNone()
    end;
}

abstract production strLiteral
e::Expr ::= s::String
{
  e.errors := [];
  e.pp = text("\"" ++ s ++ "\"");
  e.freeVars = [];
  e.value = val:strValue(s);
  e.matchRes =
    case e.matchValue of
      val:strValue(t) -> if s == t then val:listValue([]) else val:constructNone()
    | _ -> val:constructNone()
    end;
}

abstract production wildcardLiteral
e::Expr ::= 
{
  e.errors := [err(e.location, "Wildcard cannot occur in non-pattern expression")];
  e.pp = text("_");
  e.freeVars = [];
  e.value = error("Wildcard does not have a value");
  e.matchRes = val:constructSome(val:listValue([]));
}

abstract production nameLiteral
e::Expr ::= n::Name
{
  e.errors := [];
  e.patternErrors := [err(e.location, "Name cannot occur in pattern expression")];
  e.pp = text(n.name);
  e.freeVars = [n];
  e.value =
    if null(n.lookupCheck)
    then n.lookup
    else errorValue(n.lookupCheck);
}

abstract production capture
e::Expr ::= e1::Expr
{
  e.errors := [err(e.location, "Capture cannot occur in non-pattern expression")];
  e.patternErrors := e1.patternErrors;
  e.pp = cat(text("@"), e1.pp);
  e.freeVars = e1.freeVars;
  e.value = e1.value;
  e1.matchValue = e.matchValue;
  e.matchRes =
    case e1.matchRes.access(name("value", location=bogusLocation), bogusLocation) of
      listValue(vs) -> val:constructSome(val:listValue(e.matchValue :: vs))
    | _ -> val:constructNone()
    end;
}

abstract production app
e::Expr ::= f::Expr args::Exprs
{
  e.errors := f.errors ++ args.errors;
  e.patternErrors :=
    case f of
      nameLiteral(n) -> []
    | _ -> [err(f.location, "Constructor in match must be a name")]
    end ++ args.patternErrors;
  e.pp = concat([f.pp, text("("), args.pp, text(")")]);
  e.freeVars = f.freeVars ++ args.freeVars;
  
  local body::Expr =
    case f.value of
      val:functionValue(_, _, _, _, _, _, body) -> body
    end;
  body.typeEnv = 
    case f.value of
      val:functionValue(n, env, tenv, params, _, paramNames, _) -> tenv
    end; -- TODO: Find bad dependency
  body.typeNameEnv = e.typeNameEnv; -- Need for run-time type checking, TODO: Is scoping correct?
  body.env =
    case f.value of
      val:functionValue(n, env, tenv, params, _, paramNames, _) -> 
        addEnv(zipWith(pair, paramNames, args.values) ++ [pair(n, f.value)] ++ [pair("self", lazyValue(e.env, e.typeNameEnv, e, anyType()))], env)
    end;
  
  local argRuntimeErrors::[Message] =
    valuesErrors(args.values) ++
    case f.value.type of
      functionType(params, _) -> paramErrors(params, map((.type), args.values), 1, e.location)
    | _ -> [err(f.location, "Cannot apply non-function")]
    end;
  e.value =
    if null(argRuntimeErrors)
    then case f.value of
      val:functionValue(n, env, tenv, _, ret, _, _) ->
        case ret, body.value of
          dataType(_, _), structureValue(fields) -> val:nodeValue(n, left(ret), args.values, fields)
        | _, _ -> body.value
        end
    end
    else val:errorValue(argRuntimeErrors);
  
  e.matchRes = 
    case f, e.matchValue of
      nameLiteral(n), val:nodeValue(m, _, _, _) -> 
        if n.name == m
        then args.matchRes
        else val:constructNone()
    | _, _ -> val:constructNone()
    end;
  
  args.matchValue = 
    case e.matchValue of
      val:nodeValue(_, _, children, _) -> val:listValue(children)
    | _ -> error("Demanded match values when value type differs")
    end;
}

function valuesErrors
[Message] ::= vs::[Value]
{
  return
    if null(vs)
    then []
    else case head(vs) of
      errorValue(ms) -> ms
    | _ -> valuesErrors(tail(vs))
    end;
}

abstract production lambdaExpr
e::Expr ::= params::Params body::Expr
{
  e.errors := params.errors ++ body.errors;
  e.patternErrors := [err(e.location, "Lambda cannot occur in pattern expression")];
  e.pp = concat([text("fn (<params>)"), text("("), body.pp, text(")")]); -- TODO
  e.freeVars = removeAllBy(nameEq, map(name(_, location=bogusLocation), map(fst, params.defs)), body.freeVars);
  
  -- Provide dummy values for checking the declaration for errors
  params.args = [];
  body.env = addEnv(params.defs, e.env);
  
  local id::String = toString(genInt());
  e.value = val:functionValue(s"<lambda ${id}>", e.env, e.typeEnv, params.types, body.type, params.names, body);
}

abstract production addOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "+ cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("+"), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:add(e2.value, e.location);
}

abstract production subOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "- cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("-"), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:sub(e2.value, e.location);
}

abstract production mulOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "* cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("*"), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:mul(e2.value, e.location);
}

abstract production divOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "/ cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("/"), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:div(e2.value, e.location);
}

abstract production eqOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "== cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("=="), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:eq(e2.value, e.location);
}

abstract production neqOp
e::Expr ::= e1::Expr e2::Expr
{
  e.patternErrors := [err(e.location, "!= cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("!="), e2.pp]);
  forwards to notOp(eqOp(e1, e2, location=e.location), location=bogusLocation);
}

abstract production gtOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "> cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text(">"), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:gt(e2.value, e.location);
}

abstract production ltOp
e::Expr ::= e1::Expr e2::Expr
{
  e.patternErrors := [err(e.location, "< cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("<"), e2.pp]);
  forwards to notOp(gteOp(e1, e2, location=e.location), location=bogusLocation);
}

abstract production gteOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, ">= cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text(">="), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  local v1::Value = e1.value;
  local v2::Value = e2.value;
  e.value = v1.val:gt(v2, e.location).or(v1.val:eq(v2, e.location), bogusLocation);
}

abstract production lteOp
e::Expr ::= e1::Expr e2::Expr
{
  e.patternErrors := [err(e.location, "<= cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("<="), e2.pp]);
  forwards to notOp(gtOp(e1, e2, location=e.location), location=bogusLocation);
}

abstract production andOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := e1.patternErrors ++ e2.patternErrors;
  e.pp = concat([e1.pp, text("&"), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:and(e2.value, e.location);
  e1.matchValue = e.matchValue;
  e2.matchValue = e.matchValue;
  e.matchRes = 
    case e1.matchRes.access(name("value", location=bogusLocation), bogusLocation),
         e2.matchRes.access(name("value", location=bogusLocation), bogusLocation) of
      listValue(l1), listValue(l2) -> constructSome(listValue(l1 ++ l2))
    | _, _ -> constructNone()
    end;
}

abstract production orOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := e1.patternErrors ++ e2.patternErrors;
  e.pp = concat([e1.pp, text("|"), e2.pp]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  e.value = e1.value.val:or(e2.value, e.location);
  e1.matchValue = e.matchValue;
  e2.matchValue = e.matchValue;
  e.matchRes = 
    case e1.matchRes.access(name("hasValue", location=bogusLocation), bogusLocation) of
      trueValue() -> e1.matchRes
    | _ -> constructNone()
    end;
}

abstract production notOp
e::Expr ::= e1::Expr
{
  e.errors := e1.errors;
  e.patternErrors := e1.patternErrors;
  e.pp = cat(text("!"), e1.pp);
  e.freeVars = e1.freeVars;
  e.value = e1.value.not(e.location);
  e1.matchValue = e.matchValue;
  e.matchRes = 
    case e1.matchValue.access(name("hasValue", location=bogusLocation), bogusLocation) of
      val:falseValue() -> val:constructSome(val:listValue([]))
    | val:trueValue() -> val:constructNone()
    end;
}

abstract production matchOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.patternErrors;
  e.patternErrors := [err(e.location, "~ cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("~"), e2.pp]);
  e.freeVars = e1.freeVars;
  e2.matchValue = e1.value;
  e.value = e2.matchRes;
}

abstract production accessOp
e::Expr ::= e1::Expr n::Name
{
  e.errors := e1.errors;
  e.patternErrors := [err(e.location, ". cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("."), text(n.name)]);
  e.freeVars = e1.freeVars;
  e.value = e1.value.val:access(n, e.location);
}

abstract production consList
e::Expr ::= h::Expr t::Expr
{
  e.errors := h.errors ++ t.errors;
  e.patternErrors := h.patternErrors ++ t.patternErrors;
  e.pp = concat([h.pp, text("::"), t.pp]);
  e.freeVars = h.freeVars ++ t.freeVars;
  
  e.value =
    case h.value, t.value of
      errorValue(_), _ -> h.value
    | _, errorValue(_) -> t.value
    | v, val:listValue(vs) -> val:listValue(v :: vs)
    | _, _ -> val:opError("::", h.value, t.value, e.location)
    end;
  
  h.matchValue =
    case e.matchValue of
      val:listValue(h :: _) -> h
    | _ -> error("demanded match values when value type differs")
    end;
  
  t.matchValue =
    case e.matchValue of
      val:listValue(_:: t) -> val:listValue(t)
    | _ -> error("demanded match values when value type differs")
    end;
  
  e.matchRes =
    case e.matchValue of
      val:listValue(_ :: _) ->
      case h.matchRes.access(name("value", location=bogusLocation), bogusLocation),
           t.matchRes.access(name("value", location=bogusLocation), bogusLocation) of
        val:listValue(vs1), val:listValue(vs2) -> val:constructSome(val:listValue(vs1 ++ vs2))
      | _, _ -> val:constructNone()
      end
    | _ -> val:constructNone()
    end;
}

abstract production index
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "List index cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("["), e2.pp, text("]")]);
  e.freeVars = e1.freeVars ++ e2.freeVars;
  
  e.value =
    case e1.value, e2.value of
      errorValue(_), _ -> e1.value
    | _, errorValue(_) -> e2.value
    | v1, v2 -> v1.index(v2, e.location)
    end;
}

abstract production cond
e::Expr ::= cnd::Expr th::Expr el::Expr
{
  e.errors := cnd.errors ++ th.errors ++ el.errors;
  e.patternErrors := [err(e.location, "Conditional cannot occur in pattern expression")];
  e.pp = concat([text("if"), cnd.pp, text("then"), th.pp, text("else"), el.pp]);
  e.freeVars = cnd.freeVars ++ th.freeVars ++ el.freeVars;
  
  e.value =
    case cnd.value of
      errorValue(_) -> cnd.value
    | v ->
      case v.cond(e.location) of
        val:trueValue() -> th.value
      | val:falseValue() -> el.value
      | v -> v
      end
    end;
}

abstract production constructList
e::Expr ::= el::Exprs
{
  e.errors := el.errors;
  e.patternErrors := el.patternErrors;
  e.pp = concat([text("["), el.pp, text("]")]);
  e.freeVars = el.freeVars;
  
  e.value =
    if !null(el.runtimeErrors)
   	then errorValue(el.runtimeErrors)
   	else val:listValue(el.values);
  
  el.matchValue =
    case e.matchValue of
      val:listValue(vs) -> val:listValue(vs)
    | v -> val:listValue([v])
    end;
  e.matchRes = el.matchRes;
}

abstract production constructSet
e::Expr ::= el::Exprs
{
  e.errors := el.errors;
  e.patternErrors := [err(e.location, "Matching on sets is not yet implimented")];
  e.pp = concat([text("{"), el.pp, text("}")]);
  e.freeVars = el.freeVars;
  
  e.value = 
    if !null(el.runtimeErrors)
   	then errorValue(el.runtimeErrors)
   	else val:setValue(nubBy(val:eqValue, el.values));
}

abstract production declExpr
e::Expr ::= ds::Decls
{
  e.errors := ds.errors;
  e.patternErrors := [err(e.location, "Decls cannot occur in pattern expression")];
  e.pp = pp"{<decls>}"; -- TODO
  e.freeVars = error("Not yet implimented");
  
  e.value = -- TODO, check if contains errors
    case ds.returnValue of
      just(v) -> v
    | _ ->
      val:structureValue(
        zipWith(
          pair,
          map(fst, ds.rules),
          zipWith(
            lazyValue(addEnv(ds.defs, e.env), addEnv(ds.typeNameDefs, e.typeNameEnv), _, _),
            map(snd, ds.rules),
            map(snd, ds.ruleTypes))))
    end;
  
  ds.nonRecEnv = e.env;
}

synthesized attribute values::[val:Value];
synthesized attribute runtimeErrors::[Message];
synthesized attribute len::Integer;

nonterminal Exprs with env, errors, patternErrors, pp, freeVars, runtimeErrors, values, matchValue, matchRes, len;

abstract production consExpr
e::Exprs ::= h::Expr t::Exprs
{
  e.errors := h.errors ++ t.errors;
  e.patternErrors := h.patternErrors ++ t.patternErrors;
  e.pp = concat([h.pp, text(","), t.pp]);
  e.freeVars = h.freeVars ++ t.freeVars;
  
  e.runtimeErrors =
    case h.value of
      errorValue(e) -> e
    | _ -> []
    end ++ t.runtimeErrors;
  e.values = h.value :: t.values;
  h.matchValue =
    case e.matchValue of
      val:listValue(h :: t) -> h
    end;
  t.matchValue =
    case e.matchValue of
      val:listValue(h :: t) -> val:listValue(t)
    end;
  e.matchRes =
    case e.matchValue,
         h.matchRes.access(name("value", location=bogusLocation), bogusLocation),
         t.matchRes.access(name("value", location=bogusLocation), bogusLocation) of
      val:listValue([]), _, _ -> val:constructSome(val:listValue([]))
    | val:listValue(_ :: _), val:listValue(vs1), val:listValue(vs2) -> val:constructSome(val:listValue(vs1 ++ vs2))
    | _, _, _ -> val:constructNone()
    end;
  e.len = t.len + 1;
}

abstract production nilExpr
e::Exprs ::= 
{
  e.errors := [];
  e.patternErrors := [];
  e.pp = text("");
  e.freeVars = [];
  e.runtimeErrors = [];
  e.values = [];
  e.matchRes =
    case e.matchValue of
      val:listValue([]) -> val:constructSome(val:listValue([]))
    | _ -> val:constructNone()
    end;
  e.len = 0;
}