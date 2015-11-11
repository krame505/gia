grammar gia:abstractsyntax:type;

inherited attribute otherType::Type occurs on Type;
inherited attribute otherName::String occurs on Type;
synthesized attribute addType::Maybe<Type> occurs on Type;
synthesized attribute subType::Maybe<Type> occurs on Type;
synthesized attribute mulType::Maybe<Type> occurs on Type;
synthesized attribute divType::Maybe<Type> occurs on Type;
synthesized attribute eqType::Maybe<Type> occurs on Type;
synthesized attribute gtType::Maybe<Type> occurs on Type;
synthesized attribute andType::Maybe<Type> occurs on Type;
synthesized attribute orType::Maybe<Type> occurs on Type;
synthesized attribute notType::Maybe<Type> occurs on Type;
synthesized attribute indexType::Maybe<Type> occurs on Type;
synthesized attribute accessType::Maybe<Type> occurs on Type;
synthesized attribute condExists::Boolean occurs on Type;

aspect default production
t::Type ::= 
{
  t.addType = nothing();
  t.subType = nothing();
  t.mulType = nothing();
  t.divType = nothing();
  t.eqType = just(boolType());
  t.gtType = nothing();
  t.andType = nothing();
  t.orType = nothing();
  t.notType = nothing();
  t.indexType = nothing();
  t.accessType = 
    case t.otherName of
      "pp" -> just(strType())
    | "toStr" -> just(strType())
    | "internal_debug_hackUnparse" -> just(strType())
    | _ -> nothing()
    end;
  t.condExists = true;
}

aspect production anyType
t::Type ::=
{
  t.addType = just(t.otherType);
  t.subType = just(t.otherType);
  t.mulType = just(t.otherType);
  t.divType = just(t.otherType);
  t.gtType = just(boolType());
  t.andType = just(anyType());
  t.orType = just(anyType());
  t.notType = just(anyType());
  t.indexType = just(anyType());
  t.accessType = just(anyType());
}

aspect production dynamicType
t::Type ::=
{
  t.addType = just(t.otherType);
  t.subType = just(t.otherType);
  t.mulType = just(t.otherType);
  t.divType = just(t.otherType);
  t.gtType = just(boolType());
  t.andType = just(anyType());
  t.orType = just(anyType());
  t.notType = just(anyType());
  t.indexType = just(anyType());
  t.accessType = just(anyType());
}

aspect production boolType
t::Type ::=
{
  t.gtType = nothing();
  t.andType =
    case t.otherType of
      boolType() -> just(boolType())
    | anyType() -> just(boolType())
    | _ -> nothing()
    end;
  t.orType =
    case t.otherType of
      boolType() -> just(boolType())
    | anyType() -> just(boolType())
    | _ -> nothing()
    end;
  t.notType = just(boolType());
}

aspect production intType
t::Type ::=
{
  t.addType = 
    case t.otherType of
      intType() -> just(intType())
    | strType() -> just(strType())
    | anyType() -> just(anyType())
    | _ -> nothing()
    end;
  t.subType =
    case t.otherType of
      intType() -> just(intType())
    | anyType() -> just(intType())
    | _ -> nothing()
    end;
  t.mulType =
    case t.otherType of
      intType() -> just(intType())
    | strType() -> just(strType())
    | anyType() -> just(anyType())
    | _ -> nothing()
    end;
  t.divType =
    case t.otherType of
      intType() -> just(intType())
    | anyType() -> just(intType())
    | _ -> nothing()
    end;
  t.gtType = just(boolType());
}

aspect production strType
t::Type ::=
{
  t.addType =
    case t.otherType of
      intType() -> just(strType())
    | strType() -> just(strType())
    | anyType() -> just(strType())
    | _ -> nothing()
    end;
  t.mulType =
    case t.otherType of
      intType() -> just(strType())
    | anyType() -> just(strType())
    | _ -> nothing()
    end;
  t.gtType = just(boolType());
  t.indexType = just(strType());
  t.accessType = 
    case t.otherName of
      "len" -> just(intType())
    | "pp" -> just(strType())
    | "toStr" -> just(strType())
    | "internal_debug_hackUnparse" -> just(strType())
    | _ -> nothing()
    end;
}

aspect production listType
t::Type ::= t1::Type
{
  t.addType = mergeTypes(t, t.otherType);
  t.indexType = 
    case t.otherType of
      intType() -> just(t1)
    | anyType() -> just(t1)
    | _ -> nothing()
    end;
  t.accessType = 
    case t.otherName of
      "len" -> just(intType())
    | "hd" -> just(t1)
    | "tl" -> just(t)
    | "null" -> just(boolType())
    | "pp" -> just(strType())
    | "toStr" -> just(strType())
    | "internal_debug_hackUnparse" -> just(strType())
    | _ -> nothing()
    end;
}

aspect production setType
t::Type ::= t1::Type
{
  t.addType = mergeTypes(t, t.otherType);
  t.subType = mergeTypes(t, t.otherType);
  t.andType = mergeTypes(t, t.otherType);
  t.orType = mergeTypes(t, t.otherType);
  t.indexType = 
    case t.otherType of
      intType() -> just(t1)
    | anyType() -> just(t1)
    | _ -> nothing()
    end;
  t.accessType = 
    case t.otherName of
      "len" -> just(intType())
    | "pp" -> just(strType())
    | "toStr" -> just(strType())
    | "internal_debug_hackUnparse" -> just(strType())
    | _ -> nothing()
    end;
}

aspect production structureType
t::Type ::= fields::[Pair<String Type>]
{
  t.addType = checkFieldType("add", fields, t.otherType);
  t.subType = checkFieldType("sub", fields, t.otherType);
  t.mulType = checkFieldType("mul", fields, t.otherType);
  t.divType = checkFieldType("div", fields, t.otherType);
  t.eqType =
    case checkFieldType("eq", fields, t.otherType) of
      just(t) -> just(t)
    | nothing() -> just(boolType())
    end;
  t.gtType = checkFieldType("gt", fields, t.otherType);
  t.andType = checkFieldType("and", fields, t.otherType);
  t.orType = checkFieldType("or", fields, t.otherType);
  t.notType = lookupList("not", fields);
  t.indexType = checkFieldType("index", fields, t.otherType);
  t.accessType = 
    case lookupList(t.otherName, fields), t.otherName of
      just(t), _ -> just(t)
    | _, "pp" -> just(strType())
    | _, "toStr" -> just(strType())
    | _, "internal_debug_hackUnparse" -> just(strType())
    | _, _ -> nothing()
    end;
  t.condExists = true;
}

aspect production dataType
t::Type ::= n::Name fields::[Pair<String Type>]
{
  t.addType = checkFieldType("add", fields, t.otherType);
  t.subType = checkFieldType("sub", fields, t.otherType);
  t.mulType = checkFieldType("mul", fields, t.otherType);
  t.divType = checkFieldType("div", fields, t.otherType);
  t.eqType =
    case checkFieldType("eq", fields, t.otherType) of
      just(t) -> just(t)
    | nothing() -> just(boolType())
    end;
  t.gtType = checkFieldType("gt", fields, t.otherType);
  t.andType = checkFieldType("and", fields, t.otherType);
  t.orType = checkFieldType("or", fields, t.otherType);
  t.notType = lookupList("not", fields);
  t.indexType = checkFieldType("index", fields, t.otherType);
  t.accessType = 
    case lookupList(t.otherName, fields), t.otherName of
      just(t), _ -> just(t)
    | _, "pp" -> just(strType())
    | _, "toStr" -> just(strType())
    | _, "internal_debug_hackUnparse" -> just(strType())
    | _, _ -> nothing()
    end;
  t.condExists = true;
}

function checkFieldType
Maybe<Type> ::= name::String fields::[Pair<String Type>] other::Type
{
  return
    case lookupList(name, fields) of
      just(functionType([], param :: [], ret)) ->
        case convertType(other, param) of
          just(_) -> just(ret)
        | _ -> nothing()
        end
    | _ -> nothing()
    end;
}

aspect production functionType
t::Type ::= genericParams::[String] params::[Type] ret::Type
{
  t.eqType = nothing();
  t.condExists = false;
}