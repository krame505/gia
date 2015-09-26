grammar gia:abstractsyntax;

synthesized attribute name::String;
synthesized attribute lookupCheck::[Message];
synthesized attribute lookup::Value;

synthesized attribute valueLookupCheck::[Message];
synthesized attribute valueLookup::Value;

synthesized attribute nodeLookupCheck::[Message];
synthesized attribute nodeLookup::Value;

nonterminal Name with env, name, pp, lookupCheck, lookup, location;

abstract production name
n::Name ::= s::String
{
  n.name = s;
  n.pp = text(s);
  
  local lookupRes::[Value] = lookup(s, n.env);
  n.lookupCheck =
    if null(lookupRes)
    then [err(n.location, "Undefined " ++ s)]
    else [];
  n.lookup =
    if null(lookupRes)
    then error("Demanded lookup for " ++ s ++ " when lookup failed")
    else head(lookupRes);
}

synthesized attribute maybename::Maybe<Name>;
synthesized attribute hasName::Boolean;

nonterminal MaybeName with maybename, hasName, env;

abstract production justName
mn::MaybeName ::= n::Name
{
  mn.maybename = just(n);
  mn.hasName = true;
}

abstract production nothingName
mn::MaybeName ::=
{
  mn.maybename = nothing();
  mn.hasName = false;
}
