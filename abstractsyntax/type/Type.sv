grammar gia:abstractsyntax:type;

imports gia:abstractsyntax;
imports gia:abstractsyntax:env;

imports silver:langutil hiding pp;
imports silver:langutil:pp with implode as ppImplode;

type TypeEnv = Env<Type>;
type TypeDef = Def<Type>;

autocopy attribute typeEnv::TypeEnv occurs on Decls, Decl, Params, Expr, Exprs, Name;
synthesized attribute typeDefs::[TypeDef] occurs on Decls, Decl, Params;
synthesized attribute typeRecDefs::[TypeDef] occurs on Decl;

autocopy attribute typeNameEnv::TypeEnv occurs on Decls, Decl, Params, Expr, Exprs, Name;
autocopy attribute typeNameExtendsEnv::TypeEnv occurs on Decl, Decls;
synthesized attribute typeNameDefs::[TypeDef] occurs on Decls, Decl;
synthesized attribute typeNameRecDefs::[TypeDef] occurs on Decl;

nonterminal Type with pp;

abstract production anyType
t::Type ::=
{
  t.pp = text("any");
}

-- Used to denote finding multiple different types in lists, etc.  
abstract production dynamicType
t::Type ::=
{
  t.pp = text("<various>");
}

abstract production boolType
t::Type ::=
{
  t.pp = text("bool");
}

abstract production intType
t::Type ::=
{
  t.pp = text("int");
}

abstract production strType
t::Type ::=
{
  t.pp = text("str");
}

abstract production listType
t::Type ::= t1::Type
{
  t.pp =
    case t1 of
      functionType(_, _, _) -> pp"[${t1.pp}]*"
    | _ -> pp"${t1.pp}*"
    end;
}

abstract production setType
t::Type ::= t1::Type
{
  t.pp =
    case t1 of
      functionType(_, _, _) -> pp"[${t1.pp}]%"
    | _ -> pp"${t1.pp}%"
    end;
}

abstract production structureType
t::Type ::= fields::[Pair<String Type>]
{
  t.pp = pp"{${ppImplode(text(", "), map(structureEntryPP, fields))}}";
}

abstract production dataType
t::Type ::= n::Name fields::[Pair<String Type>]
{
  t.pp = pp"${n.pp} {${ppImplode(text(", "), map(structureEntryPP, fields))}}";
}

function structureEntryPP
Document ::= val::Pair<String Type>
{
  return
    case val.snd of
      anyType() -> text(val.fst)
    | t -> pp"${text(val.fst)}: ${t.pp}"
    end;
}

abstract production functionType
t::Type ::= genericParams::[String] params::[Type] ret::Type
{
  t.pp =
    if !null(genericParams)
    then pp"(${ppImplode(text(", "), map((.pp), params))}) -> ${ret.pp}"
   	else pp"(<${ppImplode(text(", "), map(text, genericParams))}>, ${ppImplode(text(", "), map((.pp), params))}) -> ${ret.pp}";
}

-- Non-canonical
abstract production namedType
t::Type ::= n::Name resolved::Type
{
  t.pp = n.pp;
  forwards to resolved;
}

abstract production extendsType
t::Type ::= n::Name t1::Type
{
  forwards to t1;
}

abstract production resolvedGenericType
t::Type ::= old::Type args::[Type] resolved::Type
{
  t.pp = pp"${old.pp}<${ppImplode(text(", "), map(actualPP, args))}>";
  forwards to resolved;
}

abstract production genericType
t::Type ::= te::TypeExpr params::[String] tenv::TypeEnv
{
  te.typeNameEnv = addEnv(zipWith(pair, params, repeat(anyType(), length(params))), tenv);
  forwards to te.type;
}

abstract production genericVarType
t::Type ::= n::Name t1::Type
{
  t.pp = pp"'${n.pp}";
  forwards to t1;
}

abstract production functionTypeWithTE
t::Type ::= genericParams::[String] params::[Type] ret::Type typeNameEnv::TypeEnv paramsTE::TypeExprs retTE::TypeExpr
{
  forwards to functionType(genericParams, params, ret);
}

function actualPP
Document ::= t::Type
{
  return
    case t of
      namedType(_, t1) -> t1.pp
    | genericVarType(_, t1) -> t1.pp
    | _ -> t.pp
    end;
}

function mergeTypesErrors
[Message] ::= t1::Type t2::Type op::String loc::Location
{
  return
    case mergeTypes(t1, t2) of
      just(t) -> []
    | nothing() -> [err(loc, s"Incompatible types for ${op}: ${show(80, t1.pp)}, ${show(80, t2.pp)}")]
    end;
}

function mergeTypesOrAny
Type ::= t1::Type t2::Type
{
  return
    case mergeTypes(t1, t2) of
      just(t) -> t
    | nothing() -> anyType()
    end;
}

function mergeTypesOrDynamic
Type ::= t1::Type t2::Type
{
  return
    case mergeTypes(t1, t2) of
      just(t) -> t
    | nothing() -> dynamicType()
    end;
}

function mergeTypes
Maybe<Type> ::= t1::Type t2::Type
{
  return
    case convertType(t1, t2), convertType(t2, t1) of
      just(t), _ -> just(t)
    | _, just(t) -> just(t)
    | _, _ -> nothing()
    end;
}

function convertTypeErrors
[Message] ::= t1::Type t2::Type op::String loc::Location
{
  return
    case convertType(t1, t2) of
      just(t) -> []
    | nothing() -> [err(loc, s"Incompatible types for ${op}: ${show(80, t1.pp)}, ${show(80, t2.pp)}")]
    end;
}

function convertTypeExpectedErrors
[Message] ::= t1::Type t2::Type op::String loc::Location
{
  return
    case convertType(t1, t2) of
      just(t) -> []
    | nothing() -> [err(loc, s"Incompatible type for ${op}: ${show(80, t1.pp)} (expected ${show(80, t2.pp)})")]
    end;
}

function convertTypeOrAny
Type ::= t1::Type t2::Type
{
  return
    case convertType(t1, t2) of
      just(t) -> t
    | nothing() -> anyType()
    end;
}

function convertType
Maybe<Type> ::= t1::Type t2::Type
{
  return 
    case t1, t2 of
      _, anyType() -> just(t1)
    | anyType(), _ -> just(t2)
    | dynamicType(), anyType() -> just(t2)
    | _, namedType(n, t3) -> 
      case convertType(t1, t3) of
        nothing() -> nothing()
      | just(t) -> just(namedType(n, t))
      end
    | boolType(), boolType() -> just(t1)
    | intType(), intType() -> just(t1)
    | strType(), strType() -> just(t1)
    | listType(s1), listType(s2) -> 
      case convertType(s1, s2) of
        just(t) -> just(listType(t))
      | nothing() -> nothing()
      end
    | setType(s1), setType(s2) -> 
      case convertType(s1, s2) of
        just(t) -> just(setType(t))
      | nothing() -> nothing()
      end
    | functionType(gp1, p1, r1), functionType(gp2, p2, r2) ->
        case foldr(andHelper, true, zipWith(stringEq, gp1, gp2)), convertParams(p1, p2), convertType(r1, r2) of
          true, just(p), just(r) -> just(functionType(gp1, p, r))
        | _, _, _ -> nothing()
        end
    | structureType(f1), structureType(f2) -> 
        case convertFields(f1, f2) of
          nothing() -> nothing()
        | just(f) -> just(structureType(f))
        end
    | dataType(_, f1), structureType(f2) -> 
        case convertFields(f1, f2) of
          nothing() -> nothing()
        | just(f) -> just(structureType(f))
        end
    | structureType(_), _ -> just(anyType()) -- Temporary hack until better checking is implimented for overloaded operators
    | dataType(_, _), _ -> just(anyType())
    | extendsType(n1, dataType(n2, f1)), extendsType(n3, dataType(n4, f2)) -> 
        if n1.name == n3.name && n2.name == n4.name
        then just(extendsType(n1, dataType(n2, f1))) -- Data types with the same name must be identical
        else nothing()
    | extendsType(n1, dataType(n2, f1)), dataType(n3, f2) -> 
        if n1.name == n3.name || n2.name == n3.name
        then just(dataType(n3, f1)) -- Data types with the same name must be identical
        else nothing()
    | dataType(n1, f1), dataType(n2, f2) -> 
        if n1.name == n2.name
        then just(dataType(n1, f1)) -- Data types with the same name must be identical
        else nothing()
    | _, _ -> nothing()
    end;
}

function convertParams
Maybe<[Type]> ::= f1::[Type] f2::[Type]
{
  return
    case f1, f2 of
      [], [] -> just([])
    | h1 :: t1, h2 :: t2 -> 
        case convertType(h1, h2), convertParams(t1, t2) of
          just(h), just(t) -> just(h :: t)
        | _, _ -> nothing()
        end
    | _, _ -> nothing()
    end;
}

function convertFields
Maybe<[Pair<String Type>]> ::= f1::[Pair<String Type>] f2::[Pair<String Type>]
{
  return
    case f2 of
      [] -> just([])
    | pair(n, h) :: t ->
        let lookupRes::[Pair<String Type>] = filter(fieldEq(pair(n, h), _), f1)
        in if null(lookupRes)
           then nothing()
           else
             case convertType(head(lookupRes).snd, h), convertFields(f1, t)  of
               just(t1), just(rest) -> just(pair(n, t1) :: rest)
             | _, _-> nothing()
             end
        end
    end;
}

function fieldEq
Boolean ::= f1::Pair<String Type> f2::Pair<String Type>
{
  return f1.fst == f2.fst && mergeTypes(f1.snd, f2.snd).isJust;
}