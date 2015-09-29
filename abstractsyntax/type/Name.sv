grammar gia:abstractsyntax:type;

synthesized attribute typeLookupCheck::[Message] occurs on Name;
synthesized attribute typeLookup::Type occurs on Name;

synthesized attribute typeNameLookupCheck::[Message] occurs on Name;
synthesized attribute typeNameLookup::Type occurs on Name;

aspect production name
n::Name ::= s::String
{
  local lookupRes::[Type] = lookup(s, n.typeEnv);
  n.typeLookupCheck =
    if null(lookupRes)
    then [err(n.location, "Undefined " ++ s)]
    else [];
  n.typeLookup =
    if null(lookupRes)
    then anyType()
    else head(lookupRes);
    
  local typeNameLookupRes::[Type] = lookup(s, n.typeNameEnv);
  n.typeNameLookupCheck =
    if null(typeNameLookupRes)
    then [err(n.location, "Undefined type " ++ s)]
    else [];
  n.typeNameLookup =
    if null(typeNameLookupRes)
    then anyType()
    else head(typeNameLookupRes);
}
