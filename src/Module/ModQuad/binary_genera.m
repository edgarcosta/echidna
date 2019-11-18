////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     BINARY GENUS CONSTRUCTORS                      //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "genus_common.m" : LatticeContent, RLattice;

////////////////////////////////////////////////////////////////////////

/*
This could be made much for efficient, with minimal effort
    for binary genera of fundamental discriminants.  For small
	discriminants this should be reasonable. 
	    */

intrinsic BinaryGenera(D::RngIntElt) -> SeqEnum
    {The sequence of genera of even primitive rank 2 
    lattices of determinant D which are primitive
    (except at 2 when D is 0 mod 4).}
    require not IsSquare(D) and D mod 4 in {0,1} :
	"Argument must be a nonsquare congruent to 0 or 1 mod 4.";
    gens := [];
    if D lt 0 then
	R1 := { f : f in ReducedForms(D) };
	R2 := { f^2 : f in R1 };
	while #R1 gt 0 do
	    f := Representative(R1);
	    M := Matrix(2,[2*f[1],f[2],f[2],2*f[3]]);
	    Append(~gens,Genus(RLattice(Lat,M)));
	    for g in R2 do
		Exclude(~R1,f*g);
	    end for;
	end while;
    else
	R1 := { f : f in ReducedOrbits(D) };
	R2 := { f[1]^2 : f in R1 };
	while #R1 gt 0 do
	    f := Representative(R1);
	    M := Matrix(2,[2*f[1],f[2],f[2],2*f[3]]);
	    Append(~gens,Genus(RLattice(Lat,M)));
	    for g in R2 do
		Exclude(~R1,ReductionOrbit(f*g));
	    end for;
	end while;
    end if;
    return gens;
end intrinsic;

intrinsic BinarySpinorGenera(D::RngIntElt) -> SeqEnum
    {}
    require not IsSquare(D) and D mod 4 in {0,1} :
	"Argument must be a nonsquare congruent to 0 or 1 mod 4.";
    return &cat[ SpinorGenera(G) : G in BinaryGenera(D) ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                 REPRESENTATIVES FOR BINARY GENERA                  //
////////////////////////////////////////////////////////////////////////

function BinaryGenusRepresentatives(L)
    // Could do better by a factor of 2 by not computing 
    // full equivalence class group.
    c := Content(L);
    if c ne 1 then
	L := ScaledLattice(L,1/c);
    end if;
    if IsOdd(L) then
	L := ScaledLattice(L,2);
	c := c/2;
    end if;
    D := -Determinant(L); 
    Q := QuadraticForms(D);
    g := Q ! [ Norm(L.1) div 2, (L.1,L.2), Norm(L.2) div 2 ];
    G, h := ClassGroup(Q); 
    H := sub< G | [ 2*x : x in G ] >;
    S := { g * h(x) : x in H };
    return [ N : N in { LatticeWithGram( c * Matrix(2,[Rationals()|
	2*f[1],Abs(f[2]),Abs(f[2]),2*f[3]])) : f in S } ];
end function;

function BinarySpinorRepresentatives(L)
    c := Content(L);
    if c ne 1 then
	L := ScaledLattice(L,1/c);
    end if;
    if IsOdd(L) then
	L := ScaledLattice(L,2);
	c := c/2;
    end if;
    D := -Determinant(L); 
    Q := QuadraticForms(D);
    g := Q ! [ Norm(L.1) div 2, (L.1,L.2), Norm(L.2) div 2 ];
    G, h := ClassGroup(Q); 
    H := sub< G | [ 4*x : x in G ] >;
    S := { g * h(x) : x in H };
    return [ N : N in { LatticeWithGram( c * Matrix(2,[Rationals()|
	2*f[1],Abs(f[2]),Abs(f[2]),2*f[3]])) : f in S } ];
end function;


////////////////////////////////////////////////////////////////////////
//                  BINARY NEIGHBOR CONSTRUCTOR                       //
////////////////////////////////////////////////////////////////////////

function BinaryNeighbors(L,p);
    if KroneckerSymbol(-Determinant(L),p) eq -1 then
	return [ Parent(L) | ];
    end if;
    c := Content(L);
    if c ne 1 then
	L := LatticeWithGram((1/c)*GramMatrix(L));
    end if;
    if IsOdd(L) then
	L := LatticeWithGram(2*GramMatrix(L));
	c := c/2;
    end if;
    D := -Determinant(L); 
    DK := FundamentalDiscriminant(D); 
    m := Isqrt(D div DK);
    error if GCD(p,m) ne 1,
	"Argument 2 must be prime to the conductor.";
    C := BinaryQuadraticForms(D);
    one := One(C);
    f := C ! [ Norm(L.1) div 2, (L.1,L.2), Norm(L.2) div 2 ];
    g := PrimeForm(C,p)^2;
    S := { C | f*g, f*g^-1 };
    return [ N : N in { LatticeWithGram( c * Matrix(2,[Rationals()|
	2*f[1],Abs(f[2]),Abs(f[2]),2*f[3]])) : f in S } ];
end function;

