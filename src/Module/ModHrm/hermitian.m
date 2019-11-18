//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          HERMITIAN MODULES                               //
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

declare type ModHrm[ModHrmElt];

declare attributes ModHrm :
    InnerProductMatrix,
    Involution,
    Module;

declare attributes ModHrmElt :
    Parent,
    Vector;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           CONSTRUCTORS                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function IsHermitianStructure(M,i)
    return true;
end function;

intrinsic HermitianModule(M::Mtrx,i::Map) -> ModHrm
    {}
    require IsHermitianStructure(M,i) :
        "Arguments must determine a Hermitian module structure.";
    V := New(ModHrm);
    V`InnerProductMatrix := M;
    V`Involution := i;
    V`Module := RowSpace(M);
    return V;
end intrinsic;

intrinsic IsCoercible(M::ModHrm,s::.) -> BoolElt, ModHrmElt
    {}
    if Type(s) eq ModHrmElt then
	if Parent(s) eq M then
	    return true, s;
	else
	    return false, "Coercion failed, incompatible parent";
	end if;
    elif Type(s) in {ModTupRngElt,ModTupFldElt,SeqEnum} then
	bool, s := IsCoercible(M`Module,s);
	if bool then
	    x := New(ModHrmElt);
	    x`Parent := M;
	    x`Vector := s;
	    return true, x;
	end if;
    elif Type(s) eq RngIntElt and s eq 0 then
	x := New(ModHrmElt);
	x`Parent := M;
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

intrinsic Print(M::ModHrm, level::MonStgElt)
    {}
    printf "Hermitian module of dimension %o\n", Dimension(M);
    printf "Inner product matrix:\n%o", M`InnerProductMatrix;
end intrinsic;

intrinsic Print(v::ModHrmElt, level::MonStgElt)
    {}
    M := Parent(v);
    printf "%o", v`Vector;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                 MEMBERSHIP AND EQUALITY TESTING                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., M::ModHrm) -> BoolElt
    {}
    if Type(x) eq ModHrmElt then
	return Parent(x) eq M;
    elif Type(x) in {ModTupRngElt,ModTupFldElt} then
	return IsCoercible(M`Module,x);
    end if;
    return false;
end intrinsic;

intrinsic 'eq' (M::ModHrm,N::ModHrm) -> BoolElt
    {}
    return M cmpeq N;
end intrinsic;

intrinsic 'eq' (u::ModHrmElt,v::ModHrmElt) -> BoolElt
    {}
    if u cmpeq v then return true; end if;
    return Parent(u) eq Parent(v) and u`Vector eq v`Vector;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        ATTRIBUTE ACCESS                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic '.'(M::ModHrm,i::RngIntElt) -> ModHrmElt
    {}
    require i gt 0 and i le Dimension(M) :
        "Argument 2 must be a positive integer at most", Dimension(M);
    v := New(ModHrmElt);
    v`Parent := M;
    v`Vector := M`Module.i;
    return v;
end intrinsic;

intrinsic Dimension(M::ModHrm) -> RngIntElt
    {}
    return Dimension(M`Module);
end intrinsic;

intrinsic ElementToSequence(u::ModHrmElt) -> SeqEnum
    {}
    return Eltseq(u`Vector);
end intrinsic;

intrinsic Parent(v::ModHrmElt) -> ModHrm
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

intrinsic Conjugate(u::ModHrmElt) -> ModHrmElt
    {}
    M := u`Parent;
    i := M`Involution;
    v := New(ModHrmElt);
    v`Parent := M;
    v`Vector := M`Module![ i(c) : c in Eltseq(u) ];
    return v;
end intrinsic;

intrinsic InnerProduct(u::ModHrmElt,v::ModHrmElt) -> RngElt
    {}
    M := Parent(u);
    require Parent(v) eq M : "Arguments are not compatible.";
    return InnerProduct(
        u`Vector*M`InnerProductMatrix,Conjugate(v)`Vector);
end intrinsic;

/*
intrinsic '*'(a::RngElt,t::ModHrmElt) -> ModHrmElt
    {}
end intrinsic;

intrinsic '*:='(s::ModHrmElt,a::RngElt)
    {}
end intrinsic;

intrinsic '+'(a::ModHrmElt,t::ModHrmElt) -> ModHrmElt
    {}
end intrinsic;

intrinsic '&+'(S::[ModHrmElt]) -> ModHrmElt
    {}
end intrinsic;
*/

/*
intrinsic '[]'(s::ModHrmElt,i::RngIntElt) -> ModHrmElt
    {}
    return Parent(s)!(s`String[i]);
end intrinsic;
*/

