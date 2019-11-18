//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       GENERALIZED STRING MONOIDS                         //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

A2ZAlph := {@ CodeToString(i) : i in [65..90] @};
aAzZAlph := A2ZAlph join {@ CodeToString(i) : i in [97..122] cat [32] @};
BinAlph := {@ IntegerToString(i) : i in [0..1] @};
OctAlph := {@ IntegerToString(i) : i in [0..7] @};
HexAlph := {@ IntegerToString(i) : i in [0..9] @} join {@"a","b","c","d","e","f"@};
R64Alph := {@ IntegerToString(i) : i in [0..63] @};

////////////////////////////////////////////////////////////////////////
//                       ATTRIBUTION DECLARATIONS                     //
////////////////////////////////////////////////////////////////////////

declare type MonStgGen[MonStgGenElt];

declare attributes MonStgGen :
    Alphabet;

declare attributes MonStgGenElt :
    Parent,
    String;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           CONSTRUCTORS                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic StringMonoid(S::SetIndx) -> MonStgGen
    {}
    M := New(MonStgGen);
    M`Alphabet := S;
    return M;
end intrinsic;

intrinsic BinaryStringMonoid() -> MonStgGen
    {}
    M := New(MonStgGen);
    M`Alphabet := BinAlph;
    return M;
end intrinsic;

intrinsic OctalStringMonoid() -> MonStgGen
    {}
    M := New(MonStgGen);
    M`Alphabet := OctAlph;
    return M;
end intrinsic;

intrinsic HexadecimalStringMonoid() -> MonStgGen
    {}
    M := New(MonStgGen);
    M`Alphabet := HexAlph;
    return M;
end intrinsic;

intrinsic Radix64StringMonoid() -> MonStgGen
    {}
    M := New(MonStgGen);
    M`Alphabet := R64Alph;
    return M;
end intrinsic;

intrinsic IsCoercible(M::MonStgGen,s::.) -> BoolElt, MonStgGenElt
    {}
    if Type(s) eq MonStgGenElt then
	if Parent(s) eq M then
	    return true, s;
	else
	    return false, "Coercion failed, incompatible parent";
	end if;
    elif Type(s) eq MonStgElt then
	if &and[ s[i] in M`Alphabet : i in [1..#s] ] then
	    m := New(MonStgGenElt);
	    m`Parent := M;
	    m`String := s;
	    return true, m;
	end if;
    end if;
    return false, "Invalid coercion";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           PRINTING                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(M::MonStgGen, level::MonStgElt)
    {}
    printf "Monoid of strings over %o", M`Alphabet;
end intrinsic;

intrinsic Print(s::MonStgGenElt, level::MonStgElt)
    {}
    M := Parent(s);
    if IsBinary(M) then
	printf "%o", &cat[ Strings() | Sprint(c) : c in Eltseq(s`String) ];
    else
	printf "%o", s`String;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                 MEMBERSHIP AND EQUALITY TESTING                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(s::., M::MonStgGen) -> BoolElt
    {}
    if Type(s) eq MonStgGenElt then
	return Parent(s) eq M;
    end if;
    return false;
end intrinsic;

intrinsic 'eq' (M::MonStgGen,N::MonStgGen) -> BoolElt
    {}
    if M cmpeq N then
	return true;
    end if;
    return M`Alphabet eq N`Alphabet;
end intrinsic;

intrinsic 'eq' (s::MonStgGenElt,t::MonStgGenElt) -> BoolElt
    {}
    if s cmpeq t then return true; end if;
    return Parent(s) eq Parent(t) and s`String eq t`String;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        ATTRIBUTE ACCESS                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic '.'(M::MonStgGen,i::RngIntElt) -> MonStgGenElt
    {}
    require i gt 0 and i le #M`Alphabet :
        "Argument 2 must be a positive integer at most", #M`Alphabet;
    s := New(MonStgGenElt);
    s`Parent := M;
    s`String := M`Alphabet[i];
    return s;
end intrinsic;

intrinsic Parent(s::MonStgGenElt) -> MonStgGen
    {}
    return s`Parent;
end intrinsic;

intrinsic String(s::MonStgGenElt) -> MonStgElt
    {The key string -- of type MonStgElt -- the cryptogrphic key.}
    if IsBinary(s`Parent) then
	ZZ := Integers();
	printf "%o", &cat[ IntegerToString(ZZ!c) : c in s`String ];
    else
	return s`String;
    end if;
end intrinsic;

intrinsic Character(s::MonStgGenElt,i::RngIntElt) -> MonStgElt
    {}
    return s`String[i];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       BOOLEAN FUNCTIONS                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsBinary(M::MonStgGen) -> BoolElt
    {}
    return M`Alphabet cmpeq BinAlph;
end intrinsic;

intrinsic IsOctal(M::MonStgGen) -> BoolElt
    {}
    return M`Alphabet cmpeq OctAlph;
end intrinsic;

intrinsic IsHexadecimal(M::MonStgGen) -> BoolElt
    {}
    return M`Alphabet cmpeq HexAlph;
end intrinsic;

intrinsic IsRadix64(M::MonStgGen) -> BoolElt
    {}
    return M`Alphabet cmpeq R64Alph;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             ARITHMETIC                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic '*'(s::MonStgGenElt,t::MonStgGenElt) -> MonStgGenElt
    {}
    require Parent(s) eq Parent(t) : "Arguments are incompatible.";
    m := New(MonStgGenElt);
    m`Parent := s`Parent;
    m`String := s`String cat t`String;
    return m;
end intrinsic;

intrinsic '*:='(s::MonStgGenElt,t::MonStgGenElt)
    {}
    require Parent(s) eq Parent(t) : "Arguments are incompatible.";
    s`String := s`String cat t`String;
end intrinsic;

intrinsic '&*'(S::[MonStgGenElt]) -> MonStgGenElt
    {}
    s := S[1]; 
    for j in [2..#S] do	s *:= S[j]; end for;
    return s;
end intrinsic;

/*
intrinsic '[]'(s::MonStgGenElt,i::RngIntElt) -> MonStgGenElt
    {}
    return Parent(s)!(s`String[i]);
end intrinsic;
*/

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             RANDOM                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Random(M::MonStgGen) -> MonStgGenElt
    {}
    s := New(MonStgGenElt);
    s`Parent := M;
    s`String := Random(M`Alphabet);
    return s;
end intrinsic;
