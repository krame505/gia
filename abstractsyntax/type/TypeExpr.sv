grammar gia:abstractsyntax:type;

synthesized attribute type::Type occurs on Expr;

inherited attribute genericTestType::Type;
synthesized attribute genericTypeDefs::[TypeDef];

nonterminal TypeExpr with typeEnv, typeNameEnv, errors, type, genericTestType, genericTypeDefs, location;

aspect default production
te::TypeExpr ::=
{
  te.genericTypeDefs = [];
}

abstract production anyTypeExpr
te::TypeExpr ::=
{
  te.errors := [];
  te.type = anyType();
}

abstract production boolTypeExpr
te::TypeExpr ::=
{
  te.errors := [];
  te.type = boolType();
}

abstract production intTypeExpr
te::TypeExpr ::=
{
  te.errors := [];
  te.type = intType();
}

abstract production strTypeExpr
te::TypeExpr ::=
{
  te.errors := [];
  te.type = strType();
}

abstract production listTypeExpr
te::TypeExpr ::= te1::TypeExpr
{
  te.errors := te1.errors;
  te.type = listType(te1.type);
  
  te1.genericTestType =
    case te.genericTestType of
      listType(t) -> t
    | _ -> anyType()
    end;
  te.genericTypeDefs = te1.genericTypeDefs;
}

abstract production setTypeExpr
te::TypeExpr ::= te1::TypeExpr
{
  te.errors := te1.errors;
  te.type = setType(te1.type);
  
  te1.genericTestType =
    case te.genericTestType of
      setType(t) -> t
    | _ -> anyType()
    end;
  te.genericTypeDefs = te1.genericTypeDefs;
}

abstract production maybeTypeExpr
te::TypeExpr ::= te1::TypeExpr
{
  te.errors := te1.errors;
  forwards to
    genericAppTypeExpr(
      nameTypeExpr(name("Maybe", location=te.location), location=te.location),
      consTypeExpr(te1, nilTypeExpr()),
      location=te.location);
}

abstract production structureTypeExpr
te::TypeExpr ::= fields::Fields
{
  te.errors := fields.errors;
  te.type = structureType(fields.fields);
  
  fields.genericTestFields = 
    case te.genericTestType of
      structureType(fs) -> fs
    | dataType(_, fs) -> fs
    | _ -> repeat(pair("", anyType()), fields.len)
    end;
  te.genericTypeDefs = fields.genericTypeDefs;
}

abstract production functionTypeExpr
te::TypeExpr ::= genericParams::[Name] params::TypeExprs ret::TypeExpr
{
  te.errors := ret.errors ++ params.errors;
  te.type = functionType(map((.name), genericParams), params.types, ret.type);
  
  params.genericTestTypes =
    case te.genericTestType of
      functionType(_, ps, _) -> ps
    | _ -> repeat(anyType(), params.len)
    end;
  ret.genericTestType =
    case te.genericTestType of
      functionType(_, _, ret) -> ret
    | _ -> anyType()
    end;
  te.genericTypeDefs = params.genericTypeDefs ++ ret.genericTypeDefs;
}

abstract production nameTypeExpr
te::TypeExpr ::= n::Name
{
  te.errors := n.typeNameLookupCheck;
  te.type = namedType(n, n.typeNameLookup);
}

abstract production genericVarTypeExpr
te::TypeExpr ::= n::Name
{
  te.errors := [];
  te.type = namedType(name("'" ++ n.name, location=n.location), anyType());
  
  te.genericTypeDefs =
    case te.genericTestType of
      anyType() -> [pair(n.name, namedType(n, anyType()))]
    | _ -> [pair(n.name, te.genericTestType)]
    end;
}

abstract production genericAppTypeExpr
te::TypeExpr ::= te1::TypeExpr args::TypeExprs
{
  te.errors := 
    case te1.type of
      genericType(te, params, tenv) -> 
        if args.len == length(params)
        then []
        else [err(te.location, s"Wrong number of generic arguments (expected ${toString(length(params))}, got ${toString(args.len)})")]
      | _ -> [err(te.location, "Type expression does not have generic parameters")]
    end ++ args.errors;
  
  local base::TypeExpr = 
    case te1.type of
      genericType(te, params, tenv) -> te
    end;
  base.typeNameEnv = 
    case te1.type of
      genericType(te, params, tenv) -> addEnv(zipWith(pair, params, args.types), tenv)
    end;
  
  te.type = resolvedGenericType(te1.type, args.types, base.type);
  
  te1.genericTestType = 
    case te.genericTestType of
      resolvedGenericType(t, _, _) -> t
    | _ -> anyType()
    end;
  args.genericTestTypes = 
    case te.genericTestType of
      resolvedGenericType(_, a, _) -> a
    | _ -> repeat(anyType(), args.len)
    end;
  te.genericTypeDefs = te1.genericTypeDefs ++ args.genericTypeDefs;
}

abstract production directTypeExpr
te::TypeExpr ::= t::Type
{
  te.errors := [];
  te.type = t;
}

-- Only used in generic type reconstruction
abstract production extendsTypeExpr
te::TypeExpr ::= n::Name te1::TypeExpr
{
  te.errors := te1.errors;
  te.type = extendsType(n, te1.type);
}

abstract production dataTypeExpr
te::TypeExpr ::= n::Name fields::Fields
{
  te.errors := fields.errors;
  te.type = dataType(n, fields.fields);
}

inherited attribute genericTestTypes::[Type];
nonterminal TypeExprs with typeEnv, typeNameEnv, errors, types, len, genericTestTypes, genericTypeDefs;

abstract production consTypeExpr
tes::TypeExprs ::= h::TypeExpr t::TypeExprs
{
  tes.errors := h.errors ++ t.errors;
  tes.types = h.type :: t.types;
  tes.len = t.len + 1;
  
  h.genericTestType = head(tes.genericTestTypes);
  t.genericTestTypes = tail(tes.genericTestTypes);
  tes.genericTypeDefs = h.genericTypeDefs ++ t.genericTypeDefs;
}

abstract production nilTypeExpr
tes::TypeExprs ::= 
{
  tes.errors := [];
  tes.types = [];
  tes.len = 0;
  tes.genericTypeDefs = [];
}

synthesized attribute fields::[Pair<String Type>];
inherited attribute genericTestFields::[Pair<String Type>];
nonterminal Fields with typeEnv, typeNameEnv, errors, fields, len, genericTestFields, genericTypeDefs;

abstract production consFields
tes::Fields ::= s::String h::TypeExpr t::Fields
{
  tes.errors := h.errors ++ t.errors;
  tes.fields = pair(s, h.type) :: t.fields;
  tes.len = t.len + 1;
  
  h.genericTestType = head(tes.genericTestFields).snd;
  t.genericTestFields = tail(tes.genericTestFields);
  tes.genericTypeDefs = h.genericTypeDefs ++ t.genericTypeDefs;
}

abstract production nilFields
tes::Fields ::= 
{
  tes.errors := [];
  tes.fields = [];
  tes.len = 0;
  tes.genericTypeDefs = [];
}

function appFields
Fields ::= f1::Fields f2::Fields
{
  return
    case f1 of
      nilFields() -> f2
    | consFields(s, h, t) -> consFields(s, h, appFields(t, f2))
    end;
}

synthesized attribute typeExprOrAny::TypeExpr;
nonterminal MaybeTypeExpr with typeEnv, typeNameEnv, errors, type, typeExprOrAny, isJust, location;

abstract production justTypeExpr
mte::MaybeTypeExpr ::= te::TypeExpr
{
  mte.errors := te.errors;
  mte.type = te.type;
  mte.typeExprOrAny = te;
  mte.isJust = true;
}

abstract production nothingTypeExpr
mte::MaybeTypeExpr ::= 
{
  mte.errors := [];
  mte.type = anyType();
  mte.typeExprOrAny = anyTypeExpr(location=mte.location);
  mte.isJust = false;
}