grammar gia:abstractsyntax:type;

synthesized attribute ruleTypes::[Pair<String Type>] occurs on Decls, Decl;
synthesized attribute returnType::Maybe<Type> occurs on Decls;

aspect production consDecl
d::Decls ::= h::Decl t::Decls
{
  d.typeDefs = h.typeDefs ++ t.typeDefs;
  d.typeNameDefs = h.typeNameDefs ++ t.typeNameDefs;
  h.typeEnv = addEnv(h.typeRecDefs ++ t.typeDefs, d.typeEnv);
  t.typeEnv = addEnv(h.typeDefs, d.typeEnv);
  h.typeNameEnv = addEnv(h.typeNameRecDefs ++ t.typeNameDefs, d.typeNameEnv);
  t.typeNameEnv = addEnv(h.typeNameDefs, d.typeNameEnv);
  t.typeNameExtendsEnv = addEnv(h.typeNameDefs, d.typeNameExtendsEnv);
  d.ruleTypes = h.ruleTypes ++ t.ruleTypes;
  d.returnType = t.returnType;
}

aspect production returnDecl
d::Decls ::= e::Expr
{
  d.returnType = just(e.type);
}

aspect production nilDecl
d::Decls ::= 
{
  d.typeDefs = [];
  d.typeNameDefs = [];
  d.ruleTypes = [];
  d.returnType = nothing();
}

aspect production decls
d::Decl ::= ds::Decls
{
  d.typeDefs = ds.typeDefs;
  d.typeRecDefs = [];
  d.typeNameDefs = ds.typeNameDefs;
  d.typeNameRecDefs = [];
  d.ruleTypes = ds.ruleTypes;
}

aspect production openDecl
d::Decl ::= e::Expr
{
  d.errors <- 
    case e.type of
      structureType(_) -> []
    | dataType(_, _) -> []
    | _ -> [err(e.location, s"Open decl expression must have structure type, but found ${show(80, e.type.pp)}")]
    end;
  d.typeDefs =
    case e.type of
      structureType(ds) -> ds
    | dataType(_, ds) -> ds
    | _ -> []
    end;
  d.typeNameDefs = [];
  d.typeNameRecDefs = [];
  d.ruleTypes =
    case e.type of
      structureType(ds) -> ds
    | dataType(_, ds) -> ds
    | _ -> []
    end;
}

aspect production typeDecl
d::Decl ::= n::Name gp::[Name] te::TypeExpr
{
  d.typeDefs = [];
  d.typeRecDefs = [];
  d.typeNameDefs =
    if null(gp)
    then [pair(n.name, te.type)]
    else [pair(n.name, genericType(te, map((.name), gp), te.typeNameEnv))];
  d.typeNameRecDefs = [pair(n.name, anyType())];
  te.typeNameEnv = addEnv(d.typeNameDefs ++ zipWith(pair, map((.name), gp), repeat(anyType(), length(gp))), d.typeNameEnv);
  d.ruleTypes = [];
}

aspect production dataTypeDecl
d::Decl ::= n::Name gp::[Name] te::TypeExpr extends::TypeExpr
{
  d.errors <-
    case te.type of
      structureType(_) -> []
    | t -> [err(te.location, s"Type in datatype declaration must be a structure, but got ${show(80, t.pp)}")]
    end ++ 
    case extends.type of
      anyType() -> [] -- Used as a dummy value to indicate no extends
    | dataType(_, _) -> []
    | _ -> [err(te.location, "Extended type in datatype declaration must be a datatype")]
    end;
  d.typeDefs = [];
  d.typeRecDefs = [];
  d.typeNameDefs = 
    if !null(gp)
    then
      case te, extends of
        structureTypeExpr(fields), dataTypeExpr(n1, extendedFields) ->
          [pair(
             n.name,
             genericType(
               extendsTypeExpr(n1, dataTypeExpr(n, appFields(fields, extendedFields), location=te.location), location=extends.location),
               map((.name), gp),
               te.typeNameEnv))]
      | structureTypeExpr(fields), _ ->
          [pair(
             n.name,
             genericType(
               dataTypeExpr(n, fields, location=te.location),
               map((.name), gp),
               te.typeNameEnv))]
      | _, _ -> [pair(n.name, anyType())]
      end
    else
      case te.type, extends.type of
        structureType(fields), dataType(n1, extendedFields) ->
          [pair(n.name, extendsType(n1, dataType(n, fields ++ extendedFields)))]
      | structureType(fields), _ -> [pair(n.name, dataType(n, fields))]
      | _, _ -> [pair(n.name, anyType())]
      end;
  d.typeNameRecDefs = [pair(n.name, anyType())];
  te.typeNameEnv = addEnv(d.typeNameDefs ++ zipWith(pair, map((.name), gp), repeat(anyType(), length(gp))), d.typeNameEnv);
  d.ruleTypes = [];
  extends.typeNameEnv = d.typeNameExtendsEnv;
}

aspect production valDecl
d::Decl ::= n::Name mte::MaybeTypeExpr e::Expr
{
  d.errors <- convertTypeExpectedErrors(e.type, mte.type, "value declaration", d.location);
  d.typeDefs = [pair(n.name, mte.type)];--convertTypeOrAny(e.type, mte.type)--TODO, fix type inference when there is no type expression
  d.typeRecDefs =
    if mte.isJust
    then [pair(n.name, mte.type)]
    else [pair(n.name, anyType())];
  d.typeNameDefs = [];
  d.typeNameRecDefs = [];
  d.ruleTypes = [pair(n.name, convertTypeOrAny(e.type, mte.type))];--convertTypeOrAny(e.type, mte.type)
}

aspect production nodeDecl
d::Decl ::= n::Name gp::[Name] p::Params mte::MaybeTypeExpr b::Expr
{
  d.errors <- 
     case b.type, mte.type of
       structureType(f1), dataType(_, f2) ->
         case convertFields(f1, f2) of
           just(_) -> []
         | _ -> [err(d.location, s"Incompatible types for expected and actual fields: ${show(80, structureType(f2).pp)}, ${show(80, structureType(f1).pp)}")]
         end
     | _, _ -> convertTypeErrors(mte.type, b.type, "expected and actual return types", d.location)
     end ++
     if length(names) != length(nubBy(stringEq, names))
     then [err(d.location, "Duplicate generic parameters")]
     else [];
  d.typeDefs =
    if mte.isJust
    then [pair(n.name, functionTypeWithTE(map((.name), gp), p.types, mte.type, d.typeNameEnv, p.typeExprs, mte.typeExprOrAny))]
    else [pair(n.name, functionTypeWithTE(map((.name), gp), p.types, b.type, d.typeNameEnv, p.typeExprs, mte.typeExprOrAny))];
  d.typeRecDefs =
    if mte.isJust
    then [pair(n.name, functionType(map((.name), gp), p.types, mte.type))]
    else [pair(n.name, functionType(map((.name), gp), p.types, anyType()))];
  d.typeNameDefs = [];
  d.typeNameRecDefs = [];
  
  local genericParams::TypeExprs = p.typeExprs;
  local defs::[TypeDef] = zipWith(pair, map((.name), gp), repeat(anyType(), length(gp))) ++ genericParams.genericTypeDefs;
  local names::[String] = map(fst, defs); 
  genericParams.genericTestTypes = repeat(anyType(), p.len);
  p.typeNameEnv = addEnv(defs, d.typeNameEnv);
  mte.typeNameEnv = p.typeNameEnv;
  b.typeNameEnv = p.typeNameEnv;
  
  -- Dummy values provided for error checking
  b.typeEnv =
    if !mte.isJust
    then addEnv(p.typeDefs ++ [pair(n.name, functionType(map((.name), gp), p.types, anyType())), pair("self", mte.type)], d.typeEnv)
    else addEnv(p.typeDefs ++ d.typeDefs ++ [pair("self", mte.type)], d.typeEnv);
  d.ruleTypes = [pair(n.name, anyType())];--e.type
}

synthesized attribute typeExprs::TypeExprs occurs on Params;

aspect production consParam
p::Params ::= h::Name mte::MaybeTypeExpr t::Params
{
  p.errors <- mte.errors;
  p.typeDefs = pair(h.name, mte.type) :: t.typeDefs; -- TODO: Typed params
  p.types = mte.type :: t.types;
  p.typeExprs = consTypeExpr(mte.typeExprOrAny, t.typeExprs);
}

aspect production nilParam
p::Params ::= 
{
  p.typeDefs = [];
  p.types = [];
  p.typeExprs = nilTypeExpr();
}