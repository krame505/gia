grammar gia:abstractsyntax:type;

imports gia:abstractsyntax;
imports gia:abstractsyntax:env;

imports silver:langutil hiding pp;
imports silver:langutil:pp with implode as ppImplode;

type TypeEnv = Env<Type>;
type TypeDef = Def<Type>;

autocopy attribute typeEnv::TypeEnv occurs on Body, Equation, Decls, Decl, Params, Expr, Exprs, Name;
synthesized attribute typeDefs::[TypeDef] occurs on Decls, Decl, Params, Body, Equation;

autocopy attribute typeNameEnv::TypeEnv occurs on Body, Equation, Decls, Decl, Params, Expr, Exprs, Name;
synthesized attribute typeNameDefs::[TypeDef] occurs on Decls, Decl;

nonterminal Type with pp;

abstract production anyType
t::Type ::=
{
  t.pp = text("any");
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
      functionType(_, _) -> pp"[${t1.pp}]*"
    | _ -> pp"${t1.pp}*"
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
t::Type ::= params::[Type] ret::Type
{
  t.pp = pp"(${ppImplode(text(", "), map((.pp), params))}) -> ${ret.pp}";
}

-- Non-canonical
abstract production namedType
t::Type ::= n::Name resolved::Type
{
  t.pp = n.pp;
  forwards to resolved;
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
    | boolType(), boolType() -> just(t1)
    | intType(), intType() -> just(t1)
    | intType(), strType() -> just(t2)
    | strType(), strType() -> just(t1)
    | listType(s1), listType(s2) -> convertType(s1, s2)
    | functionType(p1, r1), functionType(p2, r2) ->
        case convertParams(p1, p2), convertType(r1, r2) of
          just(p), just(r) -> just(functionType(p, r))
        | _, _ -> nothing()
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