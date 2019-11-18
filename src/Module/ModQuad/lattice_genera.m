////////////////////////////////////////////////////////////////////////
//                                                                    //
//             GENUS AND SPINOR GENUS SYMBOLS FOR LATTICES            //
//                            David Kohel                             //
//                        Created January 2000                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();

forward JordanDecomposition;

////////////////////////////////////////////////////////////////////////

import "genus_common.m" : LatticeContent, RLattice, UnitSquareClass;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                       Attribute declarations                       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare type SymGen;

declare attributes SymGen :
    Representative,
    IsSpinor,
    LocalGenera,
    Representatives,
    Orientations;

declare type SymGenLoc;

declare attributes SymGenLoc :
    Prime,
    ScaleFactors,
    JordanComponents;

////////////////////////////////////////////////////////////////////////
//                       Accessory Function                           //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            Coercion                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(G::SymGen,S::.) -> BoolElt, SymGen
    {}
    return false, "No coercion possible";
end intrinsic;

intrinsic IsCoercible(G::SymGenLoc,S::.) -> BoolElt, SymGenLoc
    {}
    return false, "No coercion possible";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Creation functions                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Genus(G::SymGen) -> SymGen
    {The genus of the (spinor) genus G.}
    if not G`IsSpinor then return G; end if;
    H := New(SymGen);
    H`Representative := G`Representative;
    H`IsSpinor := false;
    H`LocalGenera := G`LocalGenera;
    return H;
end intrinsic;

function GenusCommon(L,spinor)
    // The (spinor) genus of L.
    n := Rank(L);
    A := GramMatrix(L);
    det := Determinant(A);
    if Type(det) eq FldRatElt then
	det := Numerator(det)*Denominator(det);
    end if;
    error if det eq 0, "Argument must be nonsingular.";
    G := New(SymGen);
    if Type(L) ne Lat and IsPositiveDefinite(A) and n gt 0 then
	L := LatticeWithGram(A);
    end if;
    G`Representative := L;
    S := [ ];    
    for p in [ q[1] : q in Factorization(2*det) ] do
	Gp := New(SymGenLoc);
	Gp`Prime := p;
	J := pAdicDiagonalization(L,p);
	Gp`JordanComponents, Gp`ScaleFactors := JordanDecomposition(J,p);
	if IsOdd(p) or IsNontrivial(Gp) then Append(~S,Gp); end if;
    end for;
    G`LocalGenera := S; 
    G`IsSpinor := spinor;
    return G;
end function;


intrinsic Genus(L::Lat) -> SymGen
    {}
    return GenusCommon(L,false);
end intrinsic;

intrinsic Genus(L::ModTupRng) -> SymGen
    {The genus of L.}
    require Type(BaseRing(L)) in {RngInt,FldRat} :  
	"Argument must be a module over the integers or rationals."; 
    return GenusCommon(L,false);
end intrinsic;

intrinsic SpinorGenus(L::Lat) -> SymGen
    {}
    return GenusCommon(L,true);
end intrinsic;

intrinsic SpinorGenus(L::ModTupRng) -> SymGen
    {The spinor genus of L.}
    require Type(BaseRing(L)) in {RngInt,FldRat} :  
	"Argument must be a module over the integers or rationals."; 
    return GenusCommon(L,true);
end intrinsic;

intrinsic SpinorGenera(G::SymGen) -> SeqEnum
    {The spinor genera in the genus G}
    if G`IsSpinor then
	return [ G ];
    end if;
    S := SpinorGenerators(G);
    genera := [ ]; 
    V := VectorSpace(GF(2),#S);
    for e in V do
	I := [ k : k in [1..#S] | e[k] ne 0 ]; 
	L := G`Representative;
	for k in I do
	    L := CoordinateLattice(Neighbors(L,S[k])[1]);
	end for;
	H := New(SymGen);
	H`Representative := L;
	H`IsSpinor := true;
	H`LocalGenera := G`LocalGenera;
	Append(~genera,H);
    end for;
    return genera;
end intrinsic;

intrinsic LocalGenus(L::Lat,p::RngIntElt) -> SymGenLoc
    {The local genus symbol of L at p.}
    Gp := New(SymGenLoc);
    Gp`Prime := p;
    J := pAdicDiagonalization(L,p);
    Gp`JordanComponents, Gp`ScaleFactors := JordanDecomposition(J,p);
    return Gp;
end intrinsic;

intrinsic LocalGenus(L::ModTupRng,p::RngIntElt) -> SymGenLoc
    {The local genus symbol of L at p.}
    Gp := New(SymGenLoc);
    Gp`Prime := p;
    J := pAdicDiagonalization(L,p);
    Gp`JordanComponents, Gp`ScaleFactors := JordanDecomposition(J,p);
    return Gp;
end intrinsic;

function JordanDecomposition(L,p)
    n := Rank(L);
    M := GramMatrix(L);
    F := [ Parent(StandardLattice(1)) | ];
    if p ne 2 then
	D := [ QQ | M[i,i] : i in [1..n] ];
	ScaleVals := {@ Valuation(a,p) : a in D @};
	for i in ScaleVals do
	    q := p^i; 
	    Di := [ a/q : a in D | Valuation(a,p) eq i ];
	    Li := LatticeWithGram(
		DiagonalMatrix(MatrixAlgebra(Integers(),#Di),Di) );
	    Append(~F,Li);
	end for;   
	return F, [ QQ | p^i : i in ScaleVals ];
    end if;
    I := [ IntegerRing() | ]; 
    i := 1;
    while i le n do
	if i lt n and M[i,i+1] ne 0 then
	    k := Valuation(M[i,i+1],2);
	    q := 2^k;
	    r := Max([0] cat [ j : j in [1..#I] | I[j] le k ]);
	    Insert(~I,r+1,k);
	    Insert(~F,r+1,
		LatticeWithGram( MatrixAlgebra(Integers(),2)!
		[ M[i,i]/q, M[i,i+1]/q, M[i+1,i]/q, M[i+1,i+1]/q ] ) );
	    i +:= 2; 
	else
	    k := Valuation(M[i,i],2);
	    q := 2^k;
	    Append(~I,k);
	    Append(~F,
		LatticeWithGram( MatrixAlgebra(Integers(),1)!
		[ IntegerRing() | M[i,i]/q ]) );
	    i +:= 1; 
	end if;
    end while;
    ScaleVals := {@ i : i in I @};
    cmps := [ Parent(StandardLattice(1)) | 
	DirectSum([F[j] : j in [1..#F] | I[j] eq i ]) : i in ScaleVals]; 
    return cmps, [ QQ | 2^i : i in ScaleVals ];
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             Printing                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(G::SymGenLoc, level::MonStgElt)
    {}
    printf "%o-adic genus of %o", G`Prime, Representative(G);
end intrinsic;

intrinsic Print(G::SymGen, level::MonStgElt)
    {}
    if G`IsSpinor then
	printf "Spinor genus of %o", G`Representative;
    else
	printf "Genus of %o", G`Representative;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Equality testing                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'eq' (G1::SymGenLoc,G2::SymGenLoc) -> BoolElt
    {}
    return G1`Prime eq G2`Prime and
	G1`ScaleFactors eq G2`ScaleFactors and 
	G1`JordanComponents eq G2`JordanComponents;
end intrinsic;

intrinsic 'eq' (G1::SymGen,G2::SymGen) -> BoolElt
    {}
    spinor := G1`IsSpinor;
    require G2`IsSpinor eq spinor :
	"Arguments must be both genera or both spinor genera.";
    P := [ L`Prime : L in G1`LocalGenera ];
    Q := [ L`Prime : L in G2`LocalGenera ];
    if P ne Q then return false; end if;
    if not &and[ G1`LocalGenera[k] eq 
	G2`LocalGenera[k] : k in [1..#P] ] then
    return false;
end if; 
if spinor then
    if assigned G2`Representatives then
	L := G1`Representative;
	for M in Representatives(G2) do
	    if IsIsometric(L,M) then return true; end if;
	end for;
	return false;
    else 
	L := G2`Representative;
	for M in Representatives(G1) do
	    if IsIsometric(L,M) then return true; end if;
	end for;
	return false;
    end if; 
end if;
return true;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                   Attribute Access Functions                   //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic InternalRepresentative(G::SymGen) -> Lat
    {A representative lattice of G.}
    require assigned G`Representative : "No representative is known";
    return G`Representative;
end intrinsic;

intrinsic IsGenus(G::SymGen) -> BoolElt
    {True if and only if G is a genus.}
    return not G`IsSpinor;
end intrinsic;

intrinsic IsSpinorGenus(G::SymGen) -> BoolElt
    {True if and only if G is a spinor genus.}
    return G`IsSpinor;
end intrinsic;

intrinsic RelevantPrimes(G::SymGen) -> RngIntElt
    {The primes of the local genus symbols.}
    return [ ZZ | Gp`Prime : Gp in G`LocalGenera ];
end intrinsic;

intrinsic Prime(G::SymGenLoc) -> RngIntElt
    {The prime of the genus symbol.}
    return G`Prime;
end intrinsic;

intrinsic Determinant(G::SymGenLoc) -> RngIntElt
    {The p-adic determinant of G.}
    p := G`Prime;
    scls := G`ScaleFactors;
    cmps := G`JordanComponents; 
    dims := [ Dimension(J) : J in cmps ];
    ord := &*[ scls[i]^dims[i] : i in [1..#dims] ];
    if p eq 2 then
	return (&*[ Determinant(J) mod 8 : J in cmps ] mod 8) * ord;
    end if;
    // Reduce the unit part to canonical square class.
    return UnitSquareClass(
	&*[ Determinant(J) mod p : J in cmps ],p) * ord;
end intrinsic;

intrinsic Determinant(G::SymGen) -> RngIntElt
    {The determinant of G.}
    return Determinant(G`Representative);
end intrinsic;

intrinsic Dimension(G::SymGen) -> RngIntElt
    {The rank of the genus.}
    return Rank(Representative(G));
end intrinsic;

intrinsic Rank(G::SymGen) -> RngIntElt
    {The rank of the genus.}
    return Rank(Representative(G));
end intrinsic;

intrinsic Dimension(G::SymGenLoc) -> RngIntElt
    {The rank of the genus.}
    return &+[ ZZ | Rank(N) : N in G`JordanComponents ];
end intrinsic;

intrinsic Rank(G::SymGenLoc) -> RngIntElt
    {The rank of the genus.}
    return &+[ ZZ | Rank(N) : N in G`JordanComponents ];
end intrinsic;

/*
intrinsic Dimension(G::SymGenLoc,k::RngIntElt) -> RngIntElt
    {The dimension of the local genus symbol.}
    require k in [1..#G] : "Invalid range for argument 2";
    return Rank(G`JordanComponents[k]);
end intrinsic;

intrinsic Dimensions(G::SymGenLoc) -> RngIntElt
    {The dimension of the local genus symbol.}
    return [ Rank(N) : N in G`JordanComponents ];
end intrinsic;

intrinsic ScaleFactor(G::SymGenLoc,k::RngIntElt) -> RngIntElt
    {The scale factor of the k-th Jordan component.}
    require k in [1..#G] : "Invalid range for argument 2";
    return G`ScaleFactors[k];
end intrinsic;

intrinsic ScaleFactors(G::SymGenLoc) -> RngIntElt
    {The scale factors of the Jordan components.}
    return G`ScaleFactors;
end intrinsic;

intrinsic Sign(G::SymGenLoc,k::RngIntElt) -> SeqEnum
    {The sign of the k-th factor.}
    require k in [1..#G] : "Invalid range for argument 2";
    p := G`Prime;
    D := Determinant(G`JordanComponents[k]);
    return KroneckerSymbol(D,p);
end intrinsic;

intrinsic Signs(G::SymGenLoc) -> SeqEnum
    {The signs of the Jordan components.}
    p := G`Prime;
    return [ KroneckerSymbol(Determinant(J),p) 
	: J in G`JordanComponents ];
end intrinsic;

intrinsic JordanComponent(G::SymGenLoc,k::RngIntElt) -> SeqEnum
    {The k-th Jordan component of G.}
    require k in [1..#G] : "Invalid range for argument 2";
    return G`JordanComponents[k];
end intrinsic;

intrinsic JordanComponents(G::SymGenLoc) -> SeqEnum
    {The Jordan components of G.}
    return G`JordanComponents;
end intrinsic;
*/

intrinsic InternalRepresentative(G::SymGenLoc) -> Lat
    {A canonical representative for the p-adic genus, in Jordan form.}
    if Rank(G) eq 0 then
	return RSpace(ZZ,0,Matrix(0,[ZZ|]));
    end if;
    return DirectSum( [ ScaledLattice(
	G`JordanComponents[i], G`ScaleFactors[i] ) 
	: i in [1..#G`ScaleFactors] ]);
end intrinsic;

intrinsic LocalGenus(G::SymGen,p::RngIntElt) -> SeqEnum
    {The local genus symbol of G at p.}
    i := Index(RelevantPrimes(G),p);
    if i eq 0 then
	return LocalGenus(Representative(G),p);
    end if;
    return G`LocalGenera[i];
end intrinsic;

intrinsic LocalGenera(G::SymGen) -> SeqEnum
    {The local genus symbols.}
    return G`LocalGenera;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                         Functionality                          //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic Representatives(G::SymGen) -> SeqEnum
    {A sequence of representatives for the genus of G.}  
    L := G`Representative;
    require Type(L) eq Lat :
	"Representatives computed only for definite lattices.";
    if not assigned G`Representatives then
	if G`IsSpinor then
	    G`Representatives := SpinorRepresentatives(L);
	else 
	    G`Representatives := GenusRepresentatives(L);
	end if;
    end if;
    return G`Representatives;
end intrinsic;

intrinsic '#'(G::SymGen) -> RngIntElt
    {The number of genus representatives.}
    require Type(G`Representative) eq Lat :
	"Representatives enumerated only for definite lattices.";
    return #Representatives(G);
end intrinsic;

