grammar gia:abstractsyntax:type;

aspect production valueExpr
e::Expr ::= v::Value
{
  e.type = v.type;
}

aspect production errorExpr
e::Expr ::= e1::Expr
{
  e.errors <-
    case e1.type of
      strType() -> []
    | _ -> [err(e1.location, "Error expression must be a string literal")]
    end;
  e.type = anyType();
}

aspect production trueLiteral
e::Expr ::= 
{
  e.type = boolType();
}

aspect production falseLiteral
e::Expr ::= 
{
  e.type = boolType();
}

aspect production intLiteral
e::Expr ::= i::Integer
{
  e.type = intType();
}

aspect production strLiteral
e::Expr ::= s::String
{
  e.type = strType();
}

aspect production wildcardLiteral
e::Expr ::= 
{
  e.type = anyType();
}

aspect production nameLiteral
e::Expr ::= n::Name
{
  e.errors <- n.typeLookupCheck;
  e.type = n.typeLookup;
}

aspect production capture
e::Expr ::= e1::Expr
{
  e.type = e1.type;
}

aspect production app
e::Expr ::= f::Expr gargs::TypeExprs args::Exprs
{
  e.errors <- 
    case f.type of
      anyType() -> []
    | functionType(_, params, ret) -> paramErrors(params, args.types, 1, e.location)
    | _ -> [err(e.location, s"Cannot apply non-function of type ${show(80, f.type.pp)}")]
    end;
  e.patternErrors <- 
    case f.type of
      anyType() -> []
    | functionType(_, params, ret) -> paramErrors(params, args.types, 1, e.location)
    | _ -> [err(e.location, s"Cannot apply non-function of type ${show(80, f.type.pp)}")]
    end;
    
  local genericParams::TypeExprs = 
    case f.type of
      functionTypeWithTE(_, _, _, _, params, ret) -> params
    end;
  genericParams.typeNameEnv = 
    case f.type of
      functionTypeWithTE(gp, _, _, tenv, _, _) ->
        addEnv(zipWith(pair, gp, gargs.types), tenv)
    end;
  genericParams.genericTestTypes = args.types;
    
  local genericRet::TypeExpr = 
    case f.type of
      functionTypeWithTE(_, _, _, _, params, ret) -> ret
    end;
  genericRet.typeNameEnv = 
    case f.type of
      functionTypeWithTE(gp, _, _, tenv, _, _) ->
        addEnv(zipWith(pair, gp, gargs.types) ++ genericParams.genericTypeDefs, tenv)
    end;
    
  e.type =
    case f.type of
      functionTypeWithTE(_, _, _, _, params, ret) -> genericRet.type
    | functionType(_, params, ret) -> ret
    | _ -> anyType()
    end;
}

function paramErrors
[Message] ::= params::[Type] args::[Type] index::Integer loc::Location
{
  return
    case params, args of
      [], [] -> []
    | p :: params, a :: args ->
      case convertType(a, p) of
        just(_) -> []
      | nothing() ->
        [err(loc, s"Invalid type for parameter ${toString(index)} in function call (expected ${show(80, p.pp)}, got ${show(80, a.pp)})")]
      end ++ paramErrors(params, args, index + 1, loc)
    | _, _ ->
      [err(loc, s"Incorrect number of parameters in function call (expected ${toString(index + length(params) - 1)}, got ${toString(index + length(args) - 1)})")]
    end;
}

aspect production lambdaExpr
e::Expr ::= params::Params body::Expr
{
  body.typeEnv = addEnv(params.typeDefs, e.typeEnv);
  e.type = functionType([], params.types, body.type);
}

aspect production addOp
e::Expr ::= e1::Expr e2::Expr
{
  local t1::Type = e1.type;
  t1.otherType = e2.type;
  e.errors <-
    case t1.addType of
      just(_) -> []
    | nothing() -> typeError(e1.type, e2.type, "+", e.location)
    end;
  e.type = 
    case t1.addType of
      just(t) -> t
    | nothing() -> anyType()
    end;
}

aspect production subOp
e::Expr ::= e1::Expr e2::Expr
{
  --e.errors <- mergeTypesErrors(e1.type, e2.type, "-", e.location);
  e.type = mergeTypesOrAny(e1.type, e2.type);
}

aspect production mulOp
e::Expr ::= e1::Expr e2::Expr
{
  --e.errors <- mergeTypesErrors(e1.type, e2.type, "*", e.location);
  e.type = mergeTypesOrAny(e1.type, e2.type);
}

aspect production divOp
e::Expr ::= e1::Expr e2::Expr
{
  --e.errors <- mergeTypesErrors(e1.type, e2.type, "/", e.location);
  e.type = mergeTypesOrAny(e1.type, e2.type);
}

-- TODO: Type check overload is boolean
aspect production eqOp
e::Expr ::= e1::Expr e2::Expr
{
  --e.errors <- mergeTypesErrors(e1.type, e2.type, "==", e.location);
  e.type = boolType();
}

-- TODO: Type check overload is boolean
aspect production gtOp
e::Expr ::= e1::Expr e2::Expr
{
  e.type = boolType();
}

-- TODO: Type check overload is boolean
aspect production gteOp
e::Expr ::= e1::Expr e2::Expr
{
  e.type = boolType();
}

aspect production andOp
e::Expr ::= e1::Expr e2::Expr
{
  --e.errors <- mergeTypesErrors(e1.type, e2.type, "&", e.location);
    --convertTypeExpectedErrors(e1.type, boolType(), "&", e.location) ++
    --convertTypeExpectedErrors(e2.type, boolType(), "&", e.location);
  e.type = mergeTypesOrAny(e1.type, e2.type);--boolType();
}

aspect production orOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors <- mergeTypesErrors(e1.type, e2.type, "|", e.location);
    --convertTypeExpectedErrors(e1.type, boolType(), "|", e.location) ++
    --convertTypeExpectedErrors(e2.type, boolType(), "|", e.location);
  e.type = mergeTypesOrAny(e1.type, e2.type);--boolType();
}

aspect production notOp
e::Expr ::= e1::Expr
{
  --e.errors <- convertTypeExpectedErrors(e1.type, boolType(), "!", e.location);
  e.type = e1.type;--boolType();
}

aspect production matchOp
e::Expr ::= e1::Expr e2::Expr
{
  e.errors <- mergeTypesErrors(e1.type, e2.type, "~", e.location);
  local typeLookupRes::[Type] = lookup("Maybe", e.typeNameEnv);
  e.type =
    if null(typeLookupRes)
    then error("Could not find Maybe type")
    else head(typeLookupRes);
}

aspect production accessOp
e::Expr ::= e1::Expr n::Name
{
  e.errors <- if containsBy(stringEq, n.name, ["toStr", "pp", "len", "null", "hd", "tl", "toList", "internal_debug_hackUnparse", "internal_debug_dynamicType"]) then [] else --TODO
    case e1.type of
      dataType(_, fields) ->
        case lookupList(n.name, fields) of
          just(_) -> []
        | nothing() -> [err(e1.location, s"Value of type ${show(80, e1.type.pp)} does not have field ${n.name}")]
        end
    | structureType(fields) ->
        case lookupList(n.name, fields) of
          just(_) -> []
        | nothing() -> [err(e1.location, s"Value of type ${show(80, e1.type.pp)} does not have field ${n.name}")]
        end
    | anyType() -> []
    | _ -> []--[err(e1.location, s"Value of type ${show(80, e1.type.pp)} does not have fields")]
    end;
  e.type =
    case e1.type of
      dataType(_, fields) ->
        case lookupList(n.name, fields) of
          just(v) -> v
        | nothing() -> anyType()
        end
    | structureType(fields) ->
        case lookupList(n.name, fields) of
          just(v) -> v
        | nothing() -> anyType()
        end
    | _ -> anyType()
    end;
}

aspect production consList
e::Expr ::= h::Expr t::Expr
{
  e.errors <-
    case h.type, t.type of
      t1, listType(t2) -> [] --mergeTypesErrors(t1, t2, "::", e.location)
    | anyType(), listType(_) -> []
    | _, listType(anyType()) -> []
    | _, anyType() -> []
    | _, t2 -> [err(t.location, s"Second parameter to :: must be a list (got ${show(80, t2.pp)}")]
    end;
  e.type =
    case h.type, t.type of
      t1, listType(t2) -> listType(mergeTypesOrAny(t1, t2))
    | t1, _ -> listType(t1)
    end;
}

aspect production index
e::Expr ::= e1::Expr e2::Expr
{
  {-e.errors <-
    case convertType(e2.type, intType()) of
      just(_) -> []
    | nothing() -> [err(e1.location, s"Index in list access must be an int (got ${show(80, e2.type.pp)})")]
    end ++
    case e1.type of
      anyType() -> []
    | listType(_) -> []
    | _ ->[err(e1.location, s"Expression in list access must be an list (got ${show(80, e1.type.pp)})")]
    end;-}
  e.type =
    case e2.type of
      listType(t) -> t
    | setType(t) -> t
    | _ -> anyType()
    end;
}

aspect production cond
e::Expr ::= cnd::Expr th::Expr el::Expr
{
  e.errors <-
    case mergeTypes(th.type, el.type) of
      just(_) -> []
    | nothing() -> [err(el.location, s"Then and else types must be compatible (got ${show(80, th.type.pp)} and ${show(80, el.type.pp)})")]
    end;
  e.type = mergeTypesOrAny(th.type, el.type);
}

aspect production constructList
e::Expr ::= el::Exprs
{
  e.type = listType(el.mergeTypes);
}

aspect production constructSet
e::Expr ::= el::Exprs
{
  e.type = setType(el.mergeTypes);
}

aspect production declExpr
e::Expr ::= ds::Decls
{
  ds.typeNameExtendsEnv = e.typeNameEnv;
  
  e.type =
    case ds.returnType of
      just(t) -> t
    | nothing() -> structureType(ds.ruleTypes)
    end;
}

synthesized attribute types::[Type] occurs on Exprs, Params;
synthesized attribute mergeTypes::Type occurs on Exprs;

aspect production consExpr
e::Exprs ::= h::Expr t::Exprs
{
  e.types = h.type :: t.types;
  e.mergeTypes =
    case t.mergeTypes of
      dynamicType() -> dynamicType()
    | _ -> mergeTypesOrDynamic(h.type, t.mergeTypes)
    end;
}

aspect production nilExpr
e::Exprs ::= 
{
  e.types = [];
  e.mergeTypes = anyType();
}