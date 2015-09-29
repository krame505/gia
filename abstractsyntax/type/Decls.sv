grammar gia:abstractsyntax:type;

aspect production consDecl
d::Decls ::= h::Decl t::Decls
{
  d.typeDefs = h.typeDefs ++ t.typeDefs;
  d.typeNameDefs = h.typeNameDefs ++ t.typeNameDefs;
  t.typeEnv = addEnv(h.typeDefs, d.typeEnv);
  t.typeNameEnv = addEnv(h.typeNameDefs, d.typeNameEnv);
}

aspect production nilDecl
d::Decls ::= 
{
  d.typeDefs = [];
  d.typeNameDefs = [];
}

aspect production decls
d::Decl ::= ds::Decls
{
  d.typeDefs = ds.typeDefs;
  d.typeNameDefs = ds.typeNameDefs;
}

aspect production typeDecl
d::Decl ::= n::Name te::TypeExpr
{
  d.typeDefs = [];
  d.typeNameDefs = [pair(n.name, te.type)];
  te.typeNameEnv = addEnv(d.typeNameDefs, d.typeNameEnv);
}

aspect production dataTypeDecl
d::Decl ::= n::Name te::TypeExpr
{
  d.typeDefs = [];
  d.typeNameDefs = 
    case te.type of
      structureType(fields) -> [pair(n.name, dataType(n, fields))]
    | _ -> [pair(n.name, anyType())]
    end;
  te.typeNameEnv = addEnv(d.typeNameDefs, d.typeNameEnv);
}

aspect production valDecl
d::Decl ::= n::Name e::Expr
{
  d.typeDefs = [pair(n.name, e.type)];
  d.typeNameDefs = [];
}

aspect production nodeDecl
d::Decl ::= n::Name p::Params mte::MaybeTypeExpr b::Body
{
  d.errors <- mte.errors ++
     case b.returnType of
       just(t) -> convertTypeErrors(t, mte.type, "expected and actual return types", b.location)
     | nothing() ->
       if mte.isJust
       then
         case mte.type of
           dataType(_, fields) ->
             case convertFields(b.ruleTypes, fields) of
               just(_) -> []
             | _ -> [err(b.location, s"Incompatible types for expected and actual fields: ${show(80, structureType(b.ruleTypes).pp)}, ${show(80, structureType(fields).pp)}")]
             end
           | _ -> [err(mte.location, s"Node must have data type or structure type, but found ${show(80, mte.type.pp)}")]
         end
       else []
     end;
  d.typeDefs =
    if mte.isJust
    then [pair(n.name, functionType(p.types, mte.type))]
    else if b.returnType.isJust
    then [pair(n.name, functionType(p.types, b.returnType.fromJust))]
    else [pair(n.name, functionType(p.types, structureType(b.ruleTypes)))];
  d.typeNameDefs = [];
  
  -- Dummy values provided for error checking
  b.typeEnv = addEnv(p.typeDefs ++ d.typeDefs, d.typeEnv);
  b.typeNameEnv = d.typeNameEnv;
}

aspect production consParam
p::Params ::= h::Name mte::MaybeTypeExpr t::Params
{
  p.errors <- mte.errors;
  p.typeDefs = pair(h.name, anyType()) :: t.typeDefs; -- TODO: Typed params
  p.types = mte.type :: t.types;
}

aspect production nilParam
p::Params ::= 
{
  p.typeDefs = [];
  p.types = [];
}