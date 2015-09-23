grammar gia:abstractsyntax;

synthesized attribute patternErrors::[Message] with ++;
synthesized attribute value::val:Value;
inherited attribute matchValue::val:Value;
synthesized attribute matchRes::val:Value;

nonterminal Expr with env, errors, patternErrors, value, matchValue, matchRes, location;

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
  e.value = val:noneValue();
}

abstract production valueExpr
e::Expr ::= v::val:Value
{
  e.errors := [];
  e.value = v;
  e.matchRes = error("Matching on valueExpr");
}

abstract production intLiteral
e::Expr ::= i::Integer
{
  e.errors := [];
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
  e.value = val:noneValue();
  e.matchRes = val:listValue([]);
}

abstract production nameLiteral
e::Expr ::= n::Name
{
  e.errors := n.lookupCheck;
  e.patternErrors := [err(e.location, "Name cannot occur in pattern expression")];
  e.value = n.lookup.value;
}

abstract production capture
e::Expr ::= e1::Expr
{
  e.errors := [err(e.location, "Capture cannot occur in non-pattern expression")];
  e.patternErrors := e1.patternErrors;
  e.value = e1.value;
  e1.matchValue = e.matchValue;
  e.matchRes = val:listValue([e.matchValue]);
}

-- We see this in the concrete syntax, need to decide if it is a function call
-- Can't use dispatch because name and env are important for node construction
abstract production app
e::Expr ::= f::Expr args::Exprs
{
  forwards to
    case f, f.value of
      nameLiteral(n), val:constructorValue(_, _, _) -> nodeConstruct(n, args, location=e.location)
    | _, _ -> appFunction(f, args, location=e.location)
    end;
}

abstract production nodeConstruct
e::Expr ::= n::Name args::Exprs
{
  e.errors := n.lookupCheck ++ args.errors; -- TODO: Look up n? Check number of args?
  e.patternErrors := args.patternErrors;
  
  --e.value = --val:nodeValue(n, args.values, node.body); -- TODO
  e.matchRes = 
    case e.matchValue of
      val:nodeValue(m, _, _) ->
        if n.name == m
        then val:listValue(args.matchResults)
        else val:noneValue()
    | _ -> val:noneValue()
    end;
  
  args.matchValues = 
    case e.matchValue of
      val:nodeValue(_, children, _) -> children
    | _ -> error("Demanded match values when value type differs")
    end;
  
  local bodyEnv::Env =
    case n.lookup.value of
      val:constructorValue(env, params, rules) ->
        foldr(updateRuleEnv(_, bodyEnv, _), addEnv(decorate params with {args = args.values;}.defs, env), rules)
    end;
  
  e.value =
    case n.lookup.value of
      val:constructorValue(env, params, rules) ->
        val:nodeValue(n.name, args.values, map(getRuleValue(_, bodyEnv), rules))
    end;
}

function getRuleValue
Pair<String val:Value> ::= rule::Pair<String Expr> bodyEnv::Env
{
  return pair(rule.fst, decorate rule.snd with {env = bodyEnv;}.value);
}

function updateRuleEnv
Env ::= rule::Pair<String Expr> bodyEnv::Env env::Env
{
  return addEnv([pair(rule.fst, valueItem(decorate rule.snd with {env = bodyEnv;}.value))], env);
}

abstract production appFunction
e::Expr ::= f::Expr args::Exprs
{
  e.errors := f.errors ++ args.errors;
  e.patternErrors := [err(e.location, "Function call cannot occur in pattern expression")];
  
  e.value =
    case f.value of
      val:functionValue(env, params, body) ->
        if args.len != params.len
        then val:errorValue([err(e.location, s"Incorrect number of arguments (expected ${toString(params.len)}, found ${toString(args.len)}")])
        else decorate body with {env = addEnv(decorate params with {args = args.values;}.defs, env);}.value
      | _ -> val:errorValue([err(f.location, "Cannot apply non-function")])
    end;
}

abstract production lambdaExpr
e::Expr ::= params::Params body::Expr
{
  e.errors := params.errors ++ body.errors; -- TODO: Look up n? Check number of args?
  e.patternErrors := [err(e.location, "Lambda cannot occur in pattern expression")];
  
  -- Provide dummy values for checking the declaration for errors
  params.args = [];
  body.env = addEnv(params.defs, e.env);
  
  e.value = val:functionValue(e.env, params, body);
}

abstract production addOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "+ cannot occur in pattern expression")];
  e.value = e1.value.val:add(e2.value, e.location);
}

abstract production andOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "& cannot occur in pattern expression")];
  e.value = e1.value.val:and(e2.value, e.location);
}

abstract production orOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.errors;
  e.patternErrors := [err(e.location, "| cannot occur in pattern expression")];
  e.value = e1.value.val:or(e2.value, e.location);
}

abstract production matchOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors := e1.errors ++ e2.patternErrors;
  e.patternErrors := [err(e.location, "~ cannot occur in pattern expression")];
  
  e2.matchValue = e1.value;
  e.value = e2.matchRes;
}

abstract production accessOp
e::Expr ::= e1::Expr n::Name
{
  e.errors := e1.errors;
  e.patternErrors := [err(e.location, ". cannot occur in pattern expression")];
  e.value = e1.value.val:access(n, e.location);
}

abstract production consList
e::Expr ::= h::Expr t::Expr
{
  e.errors := h.errors ++ t.errors;
  e.patternErrors := h.patternErrors ++ t.patternErrors;
  
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
      val:listValue([]) -> val:noneValue()
    | val:listValue(_) ->
      case h.matchRes, t.matchRes of
        val:listValue(vs1), val:listValue(vs2) -> val:listValue(vs1 ++ vs2)
      | val:noneValue(), _ -> val:noneValue()
      | _, val:noneValue() -> val:noneValue()
      end
    end;
  
  e.value =
    case t.value of
      val:listValue(vs) -> val:listValue(h.value :: vs)
    | _ -> val:opError("::", h.value, t.value, e.location)
    end;
}

abstract production cond
e::Expr ::= cnd::Expr th::Expr el::Expr
{
  e.errors := cnd.errors ++ th.errors ++ el.errors;
  e.patternErrors := [err(e.location, "Conditional cannot occur in pattern expression")];
  
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
  
  e.value = val:listValue(el.values);
}

synthesized attribute values::[val:Value];
inherited attribute matchValues::[val:Value];
synthesized attribute matchResults::[val:Value];
synthesized attribute len::Integer;

nonterminal Exprs with env, errors, patternErrors, values, matchValues, matchResults, len;

abstract production consExpr
e::Exprs ::= h::Expr t::Exprs
{
  e.errors := h.errors ++ t.errors;
  e.patternErrors := h.patternErrors ++ t.patternErrors;
  
  e.values = h.value :: t.values;
  h.matchValue = head(e.matchValues);
  t.matchValues = tail(e.matchValues);
  e.matchResults = h.matchRes :: t.matchResults;
  e.len = t.len + 1;
}

abstract production nilExpr
e::Exprs ::= 
{
  e.errors := [];
  e.patternErrors := [];
  e.values = [];
  e.matchResults = [];
  e.len = 0;
}