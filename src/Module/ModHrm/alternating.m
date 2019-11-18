//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          ALTERNATING MODULES                             //
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

/* Created by David Kohel, October 2002 */

////////////////////////////////////////////////////////////////////////
//                       ATTRIBUTION DECLARATIONS                     //
////////////////////////////////////////////////////////////////////////

declare type ModAlt[ModAltElt];

declare attributes ModAlt :
    InnerProductMatrix,
    Involution,
    Module;

declare attributes ModAltElt :
    Parent,
    Vector;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           CONSTRUCTORS                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function IsAlternating(M)
    n := Nrows(M);
    if Ncols(M) ne n then return false; end if;
    return &and[ M[i,j] eq -M[j,i] : i,j in [1..n] | i le j ];
end function;

intrinsic AlternatingModule(M::Mtrx) -> ModAlt
    {}
    require IsAlternating(M) :
        "Argument must be an antisymmetric matrix.";
    V := New(ModAlt);
    V`InnerProductMatrix := M;
    V`Module := RowSpace(M);
    return V;
end intrinsic;

intrinsic IsCoercible(M::ModAlt,s::.) -> BoolElt, ModAltElt
    {}
    if Type(s) eq ModAltElt then
	if Parent(s) eq M then
	    return true, s;
	else
	    return false, "Coercion failed, incompatible parent";
	end if;
    elif Type(s) eq {ModTupRngElt,ModTupFldElt} then
	bool, s := IsCoercible(M`Module,s);
	if bool then
	    x := New(ModAltElt);
	    x`Vector := s;
	    return true, x;
	end if;
    elif Type(s) eq RngIntElt and s eq 0 then
	x := New(ModAltElt);
	x`Vector := M`Module!0;
	return true, x;
    end if;
    return false, "Invalid coercion";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           PRINTING                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(M::ModAlt, level::MonStgElt)
    {}
    printf "Alternating module of dimension %o\n", Dimension(M`Module);
    printf "Inner product matrix:\n%o", M`InnerProductMatrix;
end intrinsic;

intrinsic Print(v::ModAltElt, level::MonStgElt)
    {}
    M := Parent(v);
    printf "%o", v`Vector;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                 MEMBERSHIP AND EQUALITY TESTING                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., M::ModAlt) -> BoolElt
    {}
    if Type(x) eq ModAltElt then
	return Parent(x) eq M;
    elif Type(x) in {ModTupRngElt,ModTupFldElt} then
	return IsCoercible(M`Module,x);
    end if;
    return false;
end intrinsic;

intrinsic 'eq' (M::ModAlt,N::ModAlt) -> BoolElt
    {}
    return M cmpeq N;
end intrinsic;

intrinsic 'eq' (u::ModAltElt,v::ModAltElt) -> BoolElt
    {}
    if u cmpeq v then return true; end if;
    return Parent(u) eq Parent(v) and u`Vector eq v`Vector;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        ATTRIBUTE ACCESS                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic '.'(M::ModAlt,i::RngIntElt) -> ModAltElt
    {}
    require i gt 0 and i le #M`Dimension :
        "Argument 2 must be a positive integer at most", #M`Dimension;
    v := New(ModAltElt);
    v`Parent := M;
    v`Vector := M`Basis[i];
    return v;
end intrinsic;

intrinsic Parent(v::ModAltElt) -> ModAlt
    {}
    return v`Parent;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       BOOLEAN FUNCTIONS                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             ARITHMETIC                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/*
intrinsic '*'(a::RngElt,t::ModAltElt) -> ModAltElt
    {}
end intrinsic;

intrinsic '*:='(s::ModAltElt,a::RngElt)
    {}
end intrinsic;

intrinsic '+'(a::ModAltElt,t::ModAltElt) -> ModAltElt
    {}
end intrinsic;

intrinsic '&+'(S::[ModAltElt]) -> ModAltElt
    {}
end intrinsic;
*/

/*
intrinsic '[]'(s::ModAltElt,i::RngIntElt) -> ModAltElt
    {}
    return Parent(s)!(s`String[i]);
end intrinsic;
*/

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             RANDOM                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

