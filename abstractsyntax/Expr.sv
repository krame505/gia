grammar gia:abstractsyntax;

synthesized attribute patternErrors::[Message] with ++;
synthesized attribute value::val:Value;
inherited attribute matchValue::val:Value;
synthesized attribute matchRes::val:Value;

nonterminal Expr with env, errors, patternErrors, pp, value, matchValue, matchRes, location;

aspect default production
e::Expr ::=
{
  e.patternErrors := [];
  e.matchRes = val:noneValue();
}

abstract production noneLiteral
e::Expr ::= 
{
  e.errors := [];
  e.pp = text("none");
  e.value = val:noneValue();
}

abstract production valueExpr
e::Expr ::= v::val:Value
{
  e.errors := [];
  e.pp = text("<value>");
  e.value = v;
  e.matchRes = error("Matching on valueExpr");
}

abstract production intLiteral
e::Expr ::= i::Integer
{
  e.errors := [];
  e.pp = text(toString(i));
  e.value = val:intValue(i);
  e.matchRes =
    case e.matchValue of
      val:intValue(j) -> if i == j then val:listValue([]) else val:noneValue()
    | _ -> val:noneValue()
    end;
}

abstract production strLiteral
e::Expr ::= s::String
{
  e.errors := [];
  e.pp = text("\"" ++ s ++ "\"");
  e.value = val:strValue(s);
  e.matchRes =
    case e.matchValue of
      val:strValue(t) -> if s == t then val:listValue([]) else val:noneValue()
    | _ -> val:noneValue()
    end;
}

abstract production wildcardLiteral
e::Expr ::= 
{
  e.errors := [err(e.location, "Wildcard cannot occur in non-pattern expression")];
  e.pp = text("_");
  e.value = val:noneValue();
  e.matchRes = val:listValue([]);
}

abstract production nameLiteral
e::Expr ::= n::Name
{
  e.errors := n.lookupCheck;
  e.patternErrors := [err(e.location, "Name cannot occur in pattern expression")];
  e.pp = text(n.name);
  e.value = n.lookup;
}

abstract production capture
e::Expr ::= e1::Expr
{
  e.errors := [err(e.location, "Capture cannot occur in non-pattern expression")];
  e.patternErrors := e1.patternErrors;
  e.pp = cat(text("@"), e1.pp);
  e.value = e1.value;
  e1.matchValue = e.matchValue;
  e.matchRes = val:listValue([e.matchValue]);
}

abstract production app
e::Expr ::= f::Expr args::Exprs
{
  e.errors := 
    (if args.len != params.len
     then [err(e.location, s"Incorrect number of arguments (expected ${toString(params.len)}, found ${toString(args.len)})")]
     else []) ++ params.errors ++ args.errors;
  e.patternErrors :=
    case f of
      nameLiteral(n) -> []
    | _ -> [err(f.location, "Constructor in match must be a name")]
    end ++ args.patternErrors;
  e.pp = concat([f.pp, text("("), args.pp, text(")")]);
  
  local body::Body =
    case f.value of
      val:functionValue(_, _, _, body) -> body
    end;
  body.env =
    case f.value of
      val:functionValue(n, env, _, _) -> 
        addEnv(params.defs ++ [pair(n, f.value)], env)
    end;
  
  e.value =
    case f.value of
      val:functionValue(n, env, params, _) ->
        case body.returnValue of
          just(v) -> v
        | _ -> val:nodeValue(n, args.values, body.defs)
        end
    end;
  
  e.matchRes = 
    case f, e.matchValue of
      nameLiteral(n), val:nodeValue(m, _, _) -> 
        if n.name == m
        then args.matchRes
        else val:noneValue()
    | _, _ -> val:noneValue()
    end;
  
  args.matchValue = 
    case e.matchValue of
      val:nodeValue(_, children, _) -> val:listValue(children)
    | _ -> error("Demanded match values when value type differs")
    end;
  
  local params::Params =
    case f.value of
      val:functionValue(n, env, params, body) -> params
    end;
  params.args = args.values;
}

abstract production lambdaExpr
e::Expr ::= params::Params body::Expr
{
  e.errors := params.errors ++ body.errors; -- TODO: Look up n? Check number of args?
  e.patternErrors := [err(e.location, "Lambda cannot occur in pattern expression")];
  e.pp = concat([text("fn (<params>)"), text("("), body.pp, text(")")]); -- TODO
  
  -- Provide dummy values for checking the declaration for errors
  params.args = [];
  body.env = addEnv(params.defs, e.env);
  
  local id::String = toString(genInt());
  e.value = val:functionValue(s"<lambda ${id}>", e.env, params, returnBody(body, location=body.location));
}

abstract production addOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "+ cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("+"), e2.pp]);
  e.value = e1.value.val:add(e2.value, e.location);
}

abstract production subOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "- cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("-"), e2.pp]);
  e.value = e1.value.val:sub(e2.value, e.location);
}

abstract production mulOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "* cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("*"), e2.pp]);
  e.value = e1.value.val:mul(e2.value, e.location);
}

abstract production divOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "/ cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("/"), e2.pp]);
  e.value = e1.value.val:div(e2.value, e.location);
}

abstract production eqOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "== cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("=="), e2.pp]);
  e.value = e1.value.val:eq(e2.value, e.location);
}

abstract production andOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "& cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("&"), e2.pp]);
  e.value = e1.value.val:and(e2.value, e.location);
}

abstract production orOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "| cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("|"), e2.pp]);
  e.value = e1.value.val:or(e2.value, e.location);
}

abstract production matchOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.patternErrors;
  e.patternErrors := [err(e.location, "~ cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("~"), e2.pp]);
  e2.matchValue = e1.value;
  e.value = e2.matchRes;
}

abstract production accessOp
e::Expr ::= e1::Expr n::Name
{
  e.errors := e1.errors;
  e.patternErrors := [err(e.location, ". cannot occur in pattern expression")];
  e.pp = concat([e1.pp, text("."), text(n.name)]);
  e.value = e1.value.val:access(n, e.location);
}

abstract production consList
e::Expr ::= h::Expr t::Expr
{
  e.errors := h.errors ++ t.errors;
  e.patternErrors := h.patternErrors ++ t.patternErrors;
  e.pp = concat([h.pp, text("::"), t.pp]);
  
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
      val:listValue(_) ->
      case h.matchRes, t.matchRes of
        val:listValue(vs1), val:listValue(vs2) -> val:listValue(vs1 ++ vs2)
      | val:noneValue(), _ -> val:noneValue()
      | _, val:noneValue() -> val:noneValue()
      end
    | _ -> val:noneValue()
    end;
  
  e.value =
    case h.value, t.value of
      errorValue(_), _ -> h.value
    | _, errorValue(_) -> t.value
    | v, val:listValue(vs) -> val:listValue(v :: vs)
    | _, _ -> val:opError("::", h.value, t.value, e.location)
    end;
}

abstract production cond
e::Expr ::= cnd::Expr th::Expr el::Expr
{
  e.errors := cnd.errors ++ th.errors ++ el.errors;
  e.patternErrors := [err(e.location, "Conditional cannot occur in pattern expression")];
  e.pp = concat([text("if"), cnd.pp, text("then"), th.pp, text("else"), el.pp]);
  
  e.value =
    case cnd.value of
      val:noneValue() -> el.value
    | _ -> th.value
    end;
}

abstract production constructList
e::Expr ::= el::Exprs
{
  e.errors := el.errors;
  e.patternErrors := el.patternErrors;
  e.pp = concat([text("["), el.pp, text("]")]);
  
  e.value = val:listValue(el.values);
  
  el.matchValue =
    case e.matchValue of
      val:listValue(vs) -> val:listValue(vs)
    | v -> val:listValue([v])
    end;
  e.matchRes = el.matchRes;
}

synthesized attribute values::[val:Value];
synthesized attribute len::Integer;

nonterminal Exprs with env, errors, patternErrors, pp, values, matchValue, matchRes, len;

abstract production consExpr
e::Exprs ::= h::Expr t::Exprs
{
  e.errors := h.errors ++ t.errors;
  e.patternErrors := h.patternErrors ++ t.patternErrors;
  e.pp = concat([h.pp, text(","), t.pp]);
  
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
    case e.matchValue, h.matchRes, t.matchRes of
      val:listValue([]), _, _ -> val:noneValue()
    | val:listValue(_ :: _), val:listValue(vs1), val:listValue(vs2) -> val:listValue(vs1 ++ vs2)
    | _, _, _ -> val:noneValue()
    end;
  e.len = t.len + 1;
}

abstract production nilExpr
e::Exprs ::= 
{
  e.errors := [];
  e.patternErrors := [];
  e.pp = text("");
  e.values = [];
  e.matchRes =
    case e.matchValue of
      val:listValue([]) -> val:listValue([])
    | _ -> val:noneValue()
    end;
  e.len = 0;
}