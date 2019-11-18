////////////////////////////////////////////////////////////////////////
//                                                                    //
//              BOOLEAN INVARIANTS OF LATTICES AND GENERA             //
//                           David R. Kohel                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "genus_common.m" : FieldSquareClass, LatticeContent, RLattice;

////////////////////////////////////////////////////////////////////////

intrinsic IsExact(L::Lat) -> BoolElt
    {True if and only if the lattice norm takes values in an exact
    coefficient domain.}
    return Type(BaseRing(L)) in {RngInt,FldRat};
end intrinsic;
    
/*
intrinsic IsIntegral(L::Lat) -> BoolElt
    {True if and only if the lattice is an exact integral lattice.}
    return Type(BaseRing(L)) eq RngInt;
end intrinsic;
*/
    
intrinsic IsIntegral(G::SymGen) -> BoolElt
    {True if and only if the genus represents an integral lattice.}
    return IsIntegral(Representative(G));
end intrinsic;
    
////////////////////////////////////////////////////////////////////////
//    Triviality: Is the local class that of the standard matrix?     //
////////////////////////////////////////////////////////////////////////

intrinsic IsNontrivial(G::SymGenLoc) -> BoolElt
    {True if and only if G is not the trivial genus <1,..,1,1>.}
    n := Rank(G);
    if n eq 0 then
	return false; 
    elif n le 4 and Prime(G) eq 2 then
	return true;
    end if;
    return GramMatrix(Representative(G)) ne 1;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//          IsEven: Is the norm locally contained in (2)?             //
////////////////////////////////////////////////////////////////////////

intrinsic IsEven(G::SymGen) -> BoolElt
    {}
    G2 := LocalGenera(G)[1];
    if Prime(G2) ne 2 then return false; end if;
    val := Valuation(G2`ScaleFactors[1],2);
    if val ge 1 then return true; end if; 
    if val lt 0 then return false; end if; 
    return IsEven(G2`JordanComponents[1]);
end intrinsic;

intrinsic IsEven(G::SymGenLoc) -> BoolElt
    {True if and only if G has even norm form.}
    require Prime(G) eq 2 : "Argument must be a 2-adic genus.";
    if Valuation(G`ScaleFactors[1],2) ge 1 then return true; end if; 
    cmps := G`JordanComponents;
    return IsEven(cmps[1]);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//      INDEFINITENESS: Represents both +1 and -1 at infinity?        //
////////////////////////////////////////////////////////////////////////

intrinsic IsDefinite(G::SymGen) -> BoolElt
    {True if and only if G is positive definite.}
    A := GramMatrix(Representative(G));
    return IsPositiveDefinite(A) or IsNegativeDefinite(A);
end intrinsic;

intrinsic IsIndefinite(G::SymGen) -> BoolElt
    {True if and only if G is positive definite.}
    A := GramMatrix(Representative(G));
    return not (IsPositiveDefinite(A) or IsNegativeDefinite(A));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//             IsMaximal, IsIntegral, and Local Variants              //
////////////////////////////////////////////////////////////////////////

intrinsic IsIntegral(G::SymGen) -> BoolElt
    {}
    return &and[ Gp`ScaleFactors[1] ge 1 : Gp in LocalGenera(G) ];
end intrinsic;

intrinsic IsIntegral(G::SymGenLoc) -> BoolElt
    {True if and only if G is integral.}
    return G`ScaleFactors[1] ge 1;
end intrinsic;

intrinsic IspIntegral(G::SymGen,p::RngIntElt) -> BoolElt
    {True if and only if G is p-integral.}
    return LocalGenus(G,p)`ScaleFactors[1] ge 1;
end intrinsic;

intrinsic IsMaximal(G::SymGen) -> BoolElt
    {}
    require IsIntegral(G) : "Argument must be an integral genus.";
    return &and[ IsMaximal(Gp) : Gp in LocalGenera(G) ]; 
end intrinsic;

intrinsic IsMaximal(G::SymGenLoc) -> BoolElt
    {True if and only if the integral genus G is
    p-maximal at all primes p.}
    p := Prime(G);
    scls := G`ScaleFactors;
    require scls[1] ge 1 : "Argument must be p-integral.";
    if scls eq [1] then return true; end if;
    if scls[#scls] gt p then return false; end if;
    i := Index(scls,p);
    n2 := Dimension(G`JordanComponents[i]);
    if n2 le 1 then 
	return true;
    elif n2 ge 3 or p eq 2 then
	return false;
    end if;
    L := G`JordanComponents[i];
    u := FiniteField(p)!(-((L.1,L.1)/(L.2,L.2)));
    return not IsSquare(u);
end intrinsic;

intrinsic IspMaximal(G::SymGen,p::RngIntElt) -> BoolElt
    {True if and only if the p-integral genus G is p-maximal.}
    require IsPrime(p) : "Argument 2 must be prime.";
    require IspIntegral(G,p) :
       "Argument 1 must be integral with respect to argument 2.";
    return IsMaximal(LocalGenus(G,p));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//       ISOTROPIC: Represents 0 at one or all finite primes?         //
////////////////////////////////////////////////////////////////////////

function QuaternaryIsIsotropic(G)
    p := Prime(G); 
    G := MaximalSuperGenus(G);
    L1 := G`JordanComponents[1]; 
    if p ne 2 then
	if Rank(L1) ne 2 then return true; end if;
	L2 := G`JordanComponents[2];
	FF := FiniteField(p);
	return IsSquare(-FF!Determinant(L1)) or
               IsSquare(-FF!Determinant(L2));
    end if;
    // For p = 2 there is only one Jordan scalar component for 
    // the p-maximal lattices, but it might be nondiagonal.
    D := {@ Norm(v) : v in Basis(L1) @};
    if 4 in D or {@1,7@} subset D or {@3,5@} subset D then
	// L1 represents either a lattice with Gram matrix 
	// [2,1;1,4] or a diagonal lattice [1;7] or [3;5].
	return true;
    elif D eq {@2@} then
	// L1 is isometric to [2,1;1,2]+[2,1;1,2], or 
	return true;
    elif #D eq 1 then
	// At this point L1 is diagonal, so Diag = [u,u,u,u], all of 
	// which reduce to [1,1,1,1]; this shortcuts the WittInvariant
	return false;
    elif Determinant(L1) mod 8 eq 1 then
	// Diag reduces to [1,1,3,3].
	return true;
    elif D in [{@1,3@},{@1,5@},{@3,7@},{@5,7@}] then
	// Diag = [u,u,u,3u], for which (0,1,2,1) is a point mod 8, or 
	// Diag = [u,u,u,5u], for which (1,1,1,1) is a point mod 8.
	return true;
    end if;
    // All 2-maximal, reduced cases are covered above.
    assert false;
end function;


intrinsic IsIsotropic(G::SymGenLoc) -> BoolElt
    {}
    dim := Dimension(G);
    if dim ge 5 then
	return true;
    elif dim eq 4 then
	return QuaternaryIsIsotropic(G);
    elif dim eq 3 then
	return WittInvariant(G) eq 1;
    elif dim eq 2 then
	return FieldSquareClass(-Determinant(G),Prime(G));
    elif dim eq 1 then
	return false;
    end if; 
end intrinsic;

intrinsic IsIsotropic(G::SymGen) -> BoolElt
    {}
    if IsDefinite(G) then return false; end if;
    for Gp in LocalGenera(G) do
	if not IsIsotropic(Gp) then return false; end if;
    end for;
    return true;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//        SIMILARITY: Equivalent up to scalar multiplication?         //
////////////////////////////////////////////////////////////////////////

intrinsic IsSimilar(G1::SymGen,G2::SymGen) -> BoolElt
    {True if and only if G1 and G2 are similar, locally isometric
    up to a scalar.}
    dim := Rank(G1);
    if Dimension(G2) ne dim then
	return false;
    end if;
    c1 := Content(G1);
    c2 := Content(G2);
    if c1 eq c2 then
	if G1 eq G2 then
	    return true;
	end if;
	B2 := -GramMatrix(Representative(G2));
    else
	Mat := MatrixAlgebra(Integers(),dim);
	L1 := Representative(G1);
	L2 := Representative(G2);
	A1 := Mat!((1/c1)*GramMatrix(L1));
	A2 := Mat!((1/c2)*GramMatrix(L2));
	G1 := Genus(RLattice(Type(L1),A1));
	G2 := Genus(RLattice(Type(L2),A2));
	if G1 eq G2 then
	    return true;
	end if;
	B2 := -A2;
    end if;
    G2 := Genus(RLattice(ModTupRng,B2));
    return G1 eq G2;
end intrinsic;
