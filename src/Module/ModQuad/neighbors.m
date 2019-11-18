////////////////////////////////////////////////////////////////////////
//                                                                    //
//        NEIGHBOR GRAPHS, SPINOR GENUS AND GENUS REPRESENTATIVES     //
//                          David Kohel                               //
//          Kneser neighboring based on Genus of a Lattice            //
//                  Bernd Souvignier, August 1997                     //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := RationalField();

forward SetDepth, IsNonsingularVector, HasHenselLift; 
forward ExtendNeighbors, Extend2Neighbors, ExtendOddEven;
forward HasEvenNeighbor;

////////////////////////////////////////////////////////////////////////

import "spinor_group.m" : GenusGenerators;
import "binary_genera.m" : BinaryNeighbors,
    BinaryGenusRepresentatives, BinarySpinorRepresentatives;

////////////////////////////////////////////////////////////////////////

function RationalMatrix(A)
    return BaseRing(M) cmpeq ZZ
        select ChangeRing(M,QQ)!A else A where M := Parent(A);
end function;

////////////////////////////////////////////////////////////////////////

function SpinorGenusPrime(L, depth)
    // A small prime p for forming p-neighbor closure, followed 
    // by 0 if in the spinor kernel and 1 if nontrivial spinor   
    // operator (in which case a bipartite partitioning algorithm 
    // must be used.
    D := Determinant(L);
    _, _, m, n, q := SpinorKernel(L);
    p := IsOdd(L) and not HasEvenNeighbor(L, depth) select 3 else 2;
    chrs := [ m(x) : x in Generators(Domain(m)) ];
    while &or[ Evaluate(chi,p) ne 1 : chi in chrs ] do
	p := NextPrime(p);
    end while;
    return p;
end function;

////////////////////////////////////////////////////////////////////////

function OrbitWarning(Size,MinBound,MaxBound)
    if Size lt MinBound then return true, _; end if;
    size := Sprint(Size);
    errtxt :=
	"Error: requires computation of orbits of " * size * " orbits\n";
    if Size lt MaxBound then
	vprint Genus : "Warning: " * errtxt; 
	return true, _;
    end if;
    errtxt *:= "Increase Bound parameter to proceed at your own risk."; 
    return false, errtxt;
end function;

////////////////////////////////////////////////////////////////////////

function ProjectiveOrbits(G,FF)
    return LineOrbits(ChangeRing(G,FF));
end function;

////////////////////////////////////////////////////////////////////////
//          ACCESSORY FUNCTIONS FOR NEIGHBOR ENUMERATION              //
////////////////////////////////////////////////////////////////////////

procedure AdjoinNeighbor(~S, L, depth)
    // Append the lattice L to the latticre sequence S if and 
    // only if it is not isometric to another element of S.
    N := LLL(L);
    for i in [1..#S] do
	if IsIsometric(S[i], N : Depth := depth) then return; end if;
    end for;
    Append(~S, CoordinateLattice(N));
    vprintf Genus:
	"New lattice number %o of minimum %o\n", #S, Minimum(N);
end procedure;

function NeighborIndex(S, L, depth)
    for i in [1..#S] do
	if IsIsometric(S[i], L : Depth := depth) then
	    return i;       
	end if;
    end for;
    return 0;
end function;

////////////////////////////////////////////////////////////////////////
//             ENUMERATION OF SPINOR GENUS AND GENUS                  //
////////////////////////////////////////////////////////////////////////

intrinsic SpinorRepresentatives(L::Lat : 
    Depth := -1, Bound := 2^24) -> SeqEnum
    {The genus of L as isometry class representatives for the
    p-neighbors of L.}

    // Compute the genus of L by exploring the neighboring graph 
    // The Depth parameter allows to specify the value of Depth 
    // for the automorphism group and isometry calculations.

    require IsExact(L) : "Argument 1 must be an exact lattice";
    require Type(Depth) eq RngIntElt and Depth ge -1:
        "Parameter 'Depth' should be a non-negative integer.";

    if Rank(L) eq 1 then return [ L ]; end if;
    if Rank(L) eq 2 then
	return BinarySpinorRepresentatives(L);
    end if;

    L := CoordinateLattice(LLL(L));

    c := Content(L);
    if c ne 1 then L := ScaledLattice(L,1/c); end if;

    depth := SetDepth(Rank(L),Depth);
    p := SpinorGenusPrime(L, depth);
    vprint Genus: "Using spinor kernel prime", p;

    bool, errtxt := OrbitWarning(p^Rank(L),Bound div 16,Bound);
    require bool : errtxt;

    if IsOdd(L) and p eq 2 then
	return [ ScaledLattice(N,c) : N in Extend2Neighbors([L],depth) ];
    end if;
    return [ ScaledLattice(N,c) : N in ExtendNeighbors([L],p,depth) ];
end intrinsic;

intrinsic GenusRepresentatives(L::Lat : 
    Depth := -1, Bound := 2^24) -> SeqEnum
    {The genus of L as isometry class representatives for the
    p-neighbors of L.}

    // Compute the genus of L by exploring the neighboring graph 
    // The Depth parameter allows to specify the value of Depth 
    // for the automorphism group and isometry calculations.

    require IsExact(L) : "Argument 1 must be an exact lattice";
    require Type(Depth) eq RngIntElt and Depth ge -1:
        "Parameter 'Depth' should be a non-negative integer.";

    if Rank(L) eq 1 then return [ L ]; end if;
    if Rank(L) eq 2 then return BinaryGenusRepresentatives(L); end if;

    L := CoordinateLattice(LLL(L));

    c := Content(L);
    if c ne 1 then L := ScaledLattice(L,1/c); end if;

    depth := SetDepth(Rank(L),Depth);

    gens := GenusGenerators(L,depth);

    p := gens[1];
    vprint Genus : "Using prime", p;
    vprint Genus : "Auxilliary generators", Exclude(gens,p);

    bool, errtxt := OrbitWarning(p^Rank(L),Bound div 16,Bound);
    require bool : errtxt;

    S := [ L ];
    for i in [2..#gens] do
	for j in [1..#S] do
	    AdjoinNeighbor(~S, CoordinateLattice( 
                LLL(Neighbors(S[j],gens[i])[1]) ), depth);
        end for;
    end for;
    if IsOdd(L) and p eq 2 then
	return [ ScaledLattice(N,c) : N in Extend2Neighbors(S,depth) ];
    end if;
    return [ ScaledLattice(N,c) : N in ExtendNeighbors(S,p,depth) ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//          ACCESSORY FUNCTIONS FOR BUILDING NEIGHBOR GRAPHS          //
////////////////////////////////////////////////////////////////////////

function ExtendNeighbors(S,p,depth)
    // Enumerate the genus of L by exploring the neighbor graph. 
    // Valid for all even L or odd p. 
    k := 1;
    FF := FiniteField(p);
    while k le #S do
	vprint Genus: "Candidate number", k, "of", #S;
	L := S[k];
	good := Determinant(L) mod p ne 0;
	G := AutomorphismGroup(L : Depth := depth);
	for X in ProjectiveOrbits(G,FF) do
	    bool, v := HasHenselLift(L!X[1].1,p);
	    if bool then
		if good then
		    AdjoinNeighbor(~S,Neighbor(L,v,p),depth);
		elif IsNonsingularVector(v,p) then
		    AdjoinNeighbor(~S,Neighbor(L,v,p),depth);
		end if;
	    end if;
	end for;
	k +:= 1;
    end while;
    return S;
end function;

function HasEvenNeighbor(L, depth)
    G := AutomorphismGroup(L : Depth := depth);
    for X in ProjectiveOrbits(G,FiniteField(2)) do
	v := L!X[1].1;
	if Norm(v) mod 4 eq 0 then
	    if not Norm(v) mod 8 eq 0 then
		B := [ b : b in Basis(L) | (v,b) mod 2 eq 1 ];
		if #B ne 0 then
		    v +:= 2*B[1];
		end if;
	    end if;
	    if Norm(v) mod 8 eq 0 then
		N := LLL(Neighbor(L, v, 2));
		if IsEven(N) then
		    return true, CoordinateLattice(N);
		end if;
	    end if;   
	end if;
    end for;
    return false, L;
end function;

function Extend2Neighbors(S, depth)
    // Given a sequence S of odd lattices L with odd determinant,
    // enumerate the 2-neighbor closure of S.  If some L has no even
    // neighbor, the full neighboring graph is explored.

    S := [ CoordinateLattice(LLL(L)) : L in S ]; 
    for L in S do
	success := HasEvenNeighbor(L, depth);
	if not success then break; end if;
    end for;
    if success then return ExtendOddEven(S, depth); end if;
    k := 1;
    while k le #S do
	vprint Genus: "Candidate number", k, "of", #S;
	L := S[k];
	G := AutomorphismGroup(L : Depth := depth);
	for X in ProjectiveOrbits(G,FiniteField(2)) do
	    v := L!X[1].1;
	    if Norm(v) mod 4 eq 0 then
		AdjoinNeighbor(~S, Neighbor(L,v,2), depth);
		B := [ b : b in Basis(L) | (v,b) mod 2 eq 1 ];
		if #B gt 0 then
		    AdjoinNeighbor(~S, Neighbor(L,v+2*B[1],2), depth);
		end if;
	    end if;
	end for;
	k +:= 1;
    end while;
    return [ L : L in S | IsOdd(L) ];
end function;

function ExtendOddEven(LOdd, depth)
    // For L odd with odd determinant enumerate the genus of L.
    // It is first checked whether L has an even neighbor LE.
    // In that case the genus of LE is computed and the genus of L
    // obtained from the edges of the neighboring graph of LE.

    LEven := [ ];
    for L in LOdd do
	success, LE := HasEvenNeighbor(L, depth);
	error if not success, "No even neighbor in ExtendOddEven.";
	Append(~LEven,LE);
    end for;
    k := 1;
    while k le #LEven do
	vprint Genus: "Candidate number", k, "of", #LEven;
	L := LEven[k];
	G := AutomorphismGroup(L : Depth := depth);
	for X in ProjectiveOrbits(G,FiniteField(2)) do
	    v := L!X[1].1;
	    if Norm(v) mod 4 eq 0 then
		if Norm(v) mod 8 ne 0 then
		    v +:= 2*[ b : b in Basis(L) | (v,b) mod 2 eq 1 ][1];
		end if;
		AdjoinNeighbor(~LEven, Neighbor(L,v,2), depth);
		v +:= 2*[ b : b in Basis(L) | (v,b) mod 2 eq 1 ][1];
		AdjoinNeighbor(~LOdd, Neighbor(L,v,2), depth);
	    end if;
	end for;
	k +:= 1;
    end while;
    return LOdd;
end function;

////////////////////////////////////////////////////////////////////////
//                   KNESER NEIGHBORING CLOSURE                       //
////////////////////////////////////////////////////////////////////////

intrinsic NeighborClosure(L::Lat, p::RngIntElt : 
    Depth := -1, Bound := 2^24) -> SeqEnum
    {The closure of the lattice sequence under the p-neighbor relation.}

    // The Depth parameter allows to specify the value of Depth 
    // for the automorphism group and isometry calculations.

    require IsExact(L) : "Argument 1 must be an exact lattice.";
    require Rank(L) ge 2 : "Argument 1 must have rank at least 2.";
    require IsPrime(p) : "Argument 2 must be prime.";
    require Type(Depth) eq RngIntElt and Depth ge -1:
        "Parameter 'Depth' should be a non-negative integer.";

    if p lt 0 then p *:= -1; end if;
    if Rank(L) eq 2 then return BinaryGenusRepresentatives(L,p); end if;

    bool, errtxt := OrbitWarning(p^Rank(L),Bound div 16,Bound);
    require bool : errtxt;

    L := CoordinateLattice(LLL(L));

    c := Content(L);
    if c ne 1 then L := ScaledLattice(L,1/c); end if;

    depth := SetDepth(Rank(L),Depth);

    if IsOdd(L) and p eq 2 then
	return [ ScaledLattice(N,c) : N in Extend2Neighbors([L], depth) ];
    end if;
    return [ ScaledLattice(N,c) : N in ExtendNeighbors([L], p, depth) ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                      ENUMERATION OF p-NEIGHBORS                    //
////////////////////////////////////////////////////////////////////////

function twoNeighbors(L, depth)
    S := [ Parent(L) | ]; 
    L := CoordinateLattice(LLL(L)); 
    G := AutomorphismGroup(L : Depth := depth);
    for X in ProjectiveOrbits(G,FiniteField(2)) do
	v := L!X[1].1;
	if Norm(v) mod 4 eq 0 then
	    AdjoinNeighbor(~S, Neighbor(L,v,2), depth);
	    B := [ b : b in Basis(L) | (v,b) mod 2 eq 1 ];
	    if #B gt 0 then
		AdjoinNeighbor(~S, Neighbor(L,v+2*B[1],2), depth);
	    end if;
	end if;
    end for;
    return S;
end function;

intrinsic Neighbors(L::Lat, p::RngIntElt : 
    Depth := -1, Bound := 2^24) -> SeqEnum
    {The immediate p-neighbors of L.}

    require IsExact(L) : "Argument 1 must be an exact lattice";
    require IsPrime(p) : "Argument 2 must be prime.";
    require Type(Depth) eq RngIntElt and Depth ge -1:
        "Parameter 'Depth' should be a non-negative integer.";

    if p lt 0 then p *:= -1; end if;
    if Rank(L) eq 2 then return BinaryNeighbors(L,p); end if;

    bool, errtxt := OrbitWarning(p^Rank(L),Bound div 16,Bound);
    require bool : errtxt;

    L := CoordinateLattice(LLL(L)); 
	
    c := Content(L);
    if c ne 1 then L := LatticeWithGram(1/c*GramMatrix(L)); end if;

    depth := SetDepth(Rank(L),Depth);
    if p eq 2 and IsOdd(L) then
	S := twoNeighbors(L, depth);
    else
	S := [ Parent(L) | ]; 
	good := Determinant(L) mod p eq 0;
	G := AutomorphismGroup(L : Depth := depth);
	for X in ProjectiveOrbits(G,FiniteField(p)) do
	    bool, v := HasHenselLift(L!X[1].1,p);
	    if bool then
		if good or IsNonsingularVector(v,p) then
		    Append(~S, Neighbor(L,v,p));
		end if;   
	    end if;
	end for;
    end if;
    if c eq 1 then
	return S;
    else
	return [ ScaledLattice(N,c) : N in S ];
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//              ADJACENCY OPERATOR FOR p-NEIGHBOR GRAPH               //
////////////////////////////////////////////////////////////////////////

intrinsic AdjacencyMatrix(G::SymGen,p::RngIntElt : 
    Depth := -1, Bound := 2^24) -> SeqEnum
    {The p-neighbor adjacency matrix with respect to the ordered 
    sequence of representatives of the genus.}

    S := Representatives(G);

    // Compute the genus of L by exploring the neighboring graph 
    // The Depth parameter allows to specify the value of Depth 
    // for the automorphism group and isometry calculations.

    if p eq 1 then return MatrixAlgebra(ZZ,#S)!1; end if;
    require IsPrime(p) : "Argument 2 must be prime.";
    require Type(Depth) eq RngIntElt and Depth ge -1 :
        "Parameter 'Depth' should be a non-negative integer.";
    if p lt 0 then p *:= -1; end if;

    L := S[1]; 

    bool, errtxt := OrbitWarning(p^Rank(L),Bound div 16,Bound);
    require bool : errtxt;

    A := MatrixAlgebra(ZZ,#S)!0;
    if p eq 2 and IsOdd(L) then
	// Should not give up so easily!!!
	return A;
    end if;
    k := 1;
    FF := FiniteField(p);
    depth := SetDepth(Rank(L),Depth);
    while k le #S do
	vprint Genus: "Candidate number", k, "of", #S;
	L := S[k];
        good := Determinant(L) mod p ne 0;
	G := AutomorphismGroup(L : Depth := depth); 
        for X in ProjectiveOrbits(G,FF) do
	    bool, v := HasHenselLift(L!X[1].1,p);
            if bool then
		if good or IsNonsingularVector(v,p) then
		    N := LLL(Neighbor(L, v, p));
		    j := NeighborIndex(S,N,depth);
		    require j ne 0 : "Lattice sequence is not complete.";
		    A[j,k] +:= #X;
		end if;   
	    end if;
	end for;
	k +:= 1;
    end while;
    return A;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                  PRIMITIVE NEIGHBOR CONSTRUCTOR                    //
////////////////////////////////////////////////////////////////////////

intrinsic Neighbor(L::Lat, v::LatElt, p::RngIntElt) -> Lat
    {The p-neighbor of L with respect to v.}

    require IsExact(L) : "Argument 1 must be an exact lattice";
    require IsIntegral(L) : "Argument 1 is not integral";
    require IsCompatible(L, Parent(v)) and v in L:
        "Argument 2 is not an element of argument 1";
    require IsPrime(p): "Argument 3 is not a prime";
    if p lt 0 then p *:= -1; end if;
    if ZZ!Determinant(L) mod p eq 0 then
	require IsNonsingularVector(v,p) :
  	    "Argument 3 is singular point of quadratic form";
    end if;
    require ZZ!Norm(v) mod p^2 eq 0 : 
	"Norm of argument 2 must be divisible " *
	"by the square of argument 3";
    w := Coordinates(L!v);
    require &or[c mod p ne 0 : c in w] :
	"Argument 2 must be primitive";
    m := Rank(L);
    FF := FiniteField(p);
    K := Kernel(MatrixRing(FF,m)!GramMatrix(L)*RMatrixSpace(FF,m,1)!w);
    if Dimension(K) eq Degree(K) then return L; end if;
    u := Complement(Generic(K),K).1;
    C := MatrixRing(QQ,m)!( ChangeUniverse(
	Eltseq(BasisMatrix(K)),ZZ) cat [p*ZZ!u[i]: i in [1..m]]);
    B := VerticalJoin(
	C*RationalMatrix(BasisMatrix(L)),Vector(Eltseq(1/p*v)));
    return Lattice(B,RationalMatrix(InnerProductMatrix(L)));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                        ACCESSORY FUNCTIONS                         //
////////////////////////////////////////////////////////////////////////

function SetDepth(n,depth)
    if depth eq -1 then
	if n le 6 then depth := 0;
	elif n le 8 then depth := 1;
	elif n le 10 then depth := 2;
	elif n le 12 then depth := 3;
	else depth := 4;
	end if;
    end if;
    return Min(depth,10);
end function;

function IsNonsingularVector(v,p)
    L := Parent(v);
    n := Rank(L);
    f := QuadraticForm(L);
    if p eq 2 and IsEven(L) then
	f := f div 2;
    end if;
    S := [ FiniteField(p) | x : x in Eltseq(v) ];
    f := PolynomialRing(FiniteField(p),n)!f;
    for i in [1..n] do
	if Evaluate(Derivative(f,i),S) ne 0 then
	    return true;
	end if; 
    end for;
    return false;
end function;

function HasHenselLift(v,p)
    // Given a vector v with (v,v) = 0 mod p (or 4 = p^2), 
    // determines whether there exists an p-adic lifting, 
    // and if so returns a vector of norm divisible by p^2 
    // (or 8 when p = 2).
    // 
    // For p = 2, a vector of norm divisible by 4 is changed by 
    // a vector in 2*L such that the norm is divisible by 8.
    //
    // For p > 2 a vector of norm divisible by p is changed by 
    // a vector in p*L such that the norm is divisible by p^2.
    // Returns false if v does not lift p-adically.
    // 
    n := Norm(v);
    if n mod p ne 0 then return false, _; end if;
    if p eq 2 then
	if n mod 4 ne 0 then return false, _; end if;
	if n mod 8 ne 0 then
	    B := [ b : b in Basis(Parent(v)) | (v,b) mod 2 eq 1 ];
	    if #B eq 0 then return false, _; end if;
	    return true, v + 2*B[1];
	end if;
    else
	if n mod p^2 ne 0 then
	    B := [ b : b in Basis(Parent(v)) | (v,b) mod p ne 0 ];
	    if #B eq 0 then return false, _; end if;
	    return true, v - (n*Modinv(2*(v,B[1]),p) mod p^2)*B[1]; 
	end if;
   end if;
   return true, v;
end function;

