////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  LOCAL TO GLOBAL GENERA OF LATTICES                //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

ZZ := Integers();
QQ := Rationals();

import "p-adic_diagonal.m" : UnitSquareClass, RLattice;

forward GlobalBinaryGenus, GlobalTernaryGenus;
forward HasDecompositionSequence;

////////////////////////////////////////////////////////////////////////

intrinsic IsConsistent(S::[SymGenLoc]) -> BoolElt, SymGen
    {Given a sequence of local genera, returns true and
    a genus with these localizations (and elsewhere trivial)
    if the sequence is consistent with a global genus.}
    
    prms := [ ];
    hilb := [ ];
    witt := [ ];
    det := 1;
    dim := Dimension(S[1]); 
    for G in S do
	if Dimension(G) ne dim then return false; end if;
	p := Prime(G);
	scls := G`ScaleFactors;
	dims := [ Dimension(J) : J in G`JordanComponents ];
	det *:= &*[ scls[i]^dims[i] : i in [1..#dims] ];
	s := HasseInvariant(G);
	c := s;
	if dim mod 8 in {3,4} then 
	    c *:= HilbertSymbol(-1,-Determinant(G),p);
	elif dim mod 8 in {5,6} then 
	    c *:= HilbertSymbol(-1,-1,p);
	elif dim mod 8 in {7,8} then 
	    c *:= HilbertSymbol(-1,Determinant(G),p);
	end if;
	Append(~prms,p);
	Append(~hilb,s);
	Append(~witt,c);
    end for;
    sign_change := false;
    for G in S do
	if Determinant(G) ne UnitSquareClass(det,Prime(G)) then
	    sign_change := true;
	    break;
	end if;
    end for;
    if sign_change then det *:= -1; end if;
    if sign_change then
	for G in S do
	    if Determinant(G) ne UnitSquareClass(det,Prime(G)) then
		return false, _;
	    end if;
	end for;
    end if;
    if &*hilb ne 1 then return false, _; end if;
    // Local genera are now consistent, so find a genus.
    if dim eq 1 then
	L := RLattice(ModTupRng,Matrix(1,[det]));
	return true, Genus(L);
    elif dim eq 2 then
	c := &*[ Content(G) : G in S ];
	D := -ZZ!(det/c^2);
	if D mod 4 in {2,3} then D *:= 4; c /:= 2; end if;
	return true, GlobalBinaryGenus(S,D,c);
    elif dim eq 3 then
	c := &*[ Content(G) : G in S ];
	D := ZZ!(det/c^3);
	ramprms := [ prms[i] : i in [1..#prms] | witt[i] eq -1 ];
	return true, GlobalTernaryGenus(S,D,ramprms,c);
    else
	require &and[ IsMaximal(Gp) : Gp in S ] :
	    "Argument elements must be locally maximal genera " * 
	    "in dimension greater than three.";
	bool, S1, S2 := HasDecompositionSequence(S);
	require bool :
	    "Failed to find decomposition of local genera -- " * 
	    "required for recursion on lower dimension.";
	bool, G1 := IsConsistent(S1);
	require bool : "Consistency of decomposition failed.";
	bool, G2 := IsConsistent(S2);
	require bool : "Consistency of decomposition failed.";
	return true, G1 + G2;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                     HASSE AND WITT INVARIANTS                      //
////////////////////////////////////////////////////////////////////////

intrinsic HasseInvariant(G::SymGen,p::RngIntElt) -> RngIntElt
    {}
    n := Dimension(G);
    Gp := LocalGenus(G,p);
    scls := Gp`ScaleFactors;
    cmps := Gp`JordanComponents;
    dims := [ Dimension(J) : J in cmps ];
    D := [];
    for i in [1..#cmps] do
	A := GramMatrix(cmps[i]);
	if IsDiagonal(GramMatrix(A)) then
	    D cat:= [ A[j,j]*scls[i] : j in [1..dims[i]] ]; 
	else
	    // Here p = 2, and A has Gram matrix consisting 
	    // of blocks of the form [2,1;1,2] and [2,1;1,4].
	    m := dims[i] div 2;
	    D cat:= &cat[ [2*scls[i],2*(2*A[2*j,2*j]-1)*scls[i]]
		: j in [1..dims[i] div 2] ];
	end if;
    end for;
    return &*[ ZZ |
	HilbertSymbol(D[i],D[j],p) : i,j in [1..n] | i lt j ];
end intrinsic;

intrinsic HasseInvariant(G::SymGenLoc) -> RngIntElt
    {}
    p := Prime(G);
    n := Dimension(G);
    scls := G`ScaleFactors;
    cmps := G`JordanComponents;
    dims := [ Dimension(J) : J in cmps ];
    D := [];
    for i in [1..#cmps] do
	A := GramMatrix(cmps[i]);
	if IsDiagonal(GramMatrix(A)) then
	    D cat:= [ A[j,j]*scls[i] : j in [1..dims[i]] ]; 
	else
	    // Here p = 2, and A has Gram matrix consisting 
	    // of blocks of the form [2,1;1,2] and [2,1;1,4].
	    m := dims[i] div 2;
	    D cat:= &cat[ [2*scls[i],2*(2*A[2*j,2*j]-1)*scls[i]]
		: j in [1..dims[i] div 2] ];
	end if;
    end for;
    return &*[ ZZ |
	HilbertSymbol(D[i],D[j],p) : i,j in [1..n] | i lt j ];
end intrinsic;

intrinsic WittInvariant(G::SymGen,p::RngIntElt) -> RngIntElt
    {}
    n := Dimension(G);
    s := HasseInvariant(G,p);
    if n mod 8 in {1,2} then
	c := s;
    elif n mod 8 in {3,4} then 
	c := s * HilbertSymbol(-1,-Determinant(G),p);
    elif n mod 8 in {5,6} then 
	c := s * HilbertSymbol(-1,-1,p);
    else
	c := s * HilbertSymbol(-1,Determinant(G),p);
    end if;
    return c;
end intrinsic;

intrinsic WittInvariant(G::SymGenLoc) -> RngIntElt
    {}
    p := Prime(G);
    n := Dimension(G);
    s := HasseInvariant(G);
    if n mod 8 in {1,2} then
	c := s;
    elif n mod 8 in {3,4} then 
	c := s * HilbertSymbol(-1,-Determinant(G),p);
    elif n mod 8 in {5,6} then 
	c := s * HilbertSymbol(-1,-1,p);
    else
	c := s * HilbertSymbol(-1,Determinant(G),p);
    end if;
    return c;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                        GLOBAL REPRESENTATIVE                       //
////////////////////////////////////////////////////////////////////////

intrinsic GlobalRepresentative(S::[SymGenLoc]) -> ModTupRng
    {Given a consistent sequence of local genera, returns a lattice 
    which represents the genus globally.}
    bool, L := IsConsistent(S);
    require bool : "Argument must form a consistent system.";
    return L;
end intrinsic;

function GlobalBinaryGenus(S,D,c)
    // Given a consistent sequence S of local genera, the
    // precomputed determinant D and content c, returns the 
    // genus G of binary lattices consistent with the
    // sequence S of local genera.
    M := c*Matrix(2,[2,t,t,(t-D) div 2]) where t := D mod 2; 
    G := Genus(RLattice(ModTupRng,M));
    if &and[ LocalGenus(G,Prime(Gp)) eq Gp : Gp in S ] then
	return G;
    end if;
    p := 2;
    Q := QuadraticForms(D);
    while true do
	if KroneckerSymbol(D,p) eq 1 and Valuation(c,p) eq 0 then
	    f := PrimeForm(Q,p);
	    M := c*Matrix(2,[2*f[1],f[2],f[2],2*f[3]]);
	    G := Genus(RLattice(ModTupRng,M));
	    if &and[ LocalGenus(G,Prime(Gp)) eq Gp : Gp in S ] then
		return G;
	    end if;
	end if;
	p := NextPrime(p);
    end while;
    return G;
end function;

function IsLocallyIsometric(L,M,p)
    bool := LocalGenus(L,p) eq LocalGenus(M,p);
    return bool; 
end function;

function LocalRepresentation(L,c,p)
    FF := FiniteField(p);
    q := p^Valuation(c,p);
    M := MatrixAlgebra(FF,Degree(L))!((1/q)*GramMatrix(L));
    return M, c;
end function;

function GlobalTernaryGenus(S,D,ramprms,c);
    // PRE: A sequence S of local genera of determinent D 
    // (with the cube of the content removed), the ramified 
    // primes ramprms, and the content c of the genus.
    // POST: A genus representing the local genera S.
    S := [ ScaledGenus(Gp,1/c) : Gp in S ];
    A := GramMatrix(MaximalOrder(QuaternionAlgebra(&*ramprms)));
    B := D*Matrix(3,[ A[1,1]*A[i,j]-A[1,i]*A[1,j] : i,j in [2..4] ]);
    M := MaximalSuperLattice(RLattice(ModTupRng,B));
    for Gp in S do
	p := Prime(Gp);
	Lp := Representative(Gp); 
	Mp := pMaximalSuperLattice(Lp,p);
	bool := IsLocallyIsometric(Mp,M,p);
	assert bool;
	// Find local isometries Lp -> M
	/*
	// This is unfinished.
	if p ne 2 then
	    LocalRepresentation(M,Norm(Lp.1),p);
	end if;
	*/
    end for;
    return ScaledGenus(Genus(M),c);
end function;

////////////////////////////////////////////////////////////////////////

function HasLocalSplitting(G,c)
    // Given a local genus G and a candidate representation
    // number c, determine whether G splits as <c> + G2,
    // and if so returns the genera <c> and G2.
    n := Rank(G);
    p := Prime(G);
    scls := G`ScaleFactors;
    cmps := G`JordanComponents;
    i := Index(scls,p^Valuation(c,p));
    if i eq 0 then return false, _, _; end if;
    if #scls eq 1 then
	q := scls[1];
	A := GramMatrix(cmps[1]);
	D := [ QQ | A[i,i] : i in [1..n] ];
	D[n] *:= (c/q)*D[1];
	D2 := q*DiagonalMatrix(D[[2..n]]);
	assert IsDiagonal(A);
	G1 := LocalGenus(RLattice(ModTupRng,Matrix(1,[c])),p);
	G2 := LocalGenus(RLattice(ModTupRng,D2),p);
	return true, G1, G2;
    end if;
    G1 := LocalGenus(ScaledLattice(cmps[i],scls[i]),p);
    G2 := &+[ LocalGenus(ScaledLattice(cmps[j],scls[j]),p) :
	j in [1..#scls] | j ne i ]; 
    if Rank(G1) ne 1 then
	bool, G1, H2 := HasLocalSplitting(G1,c); 
	G2 +:= H2;
    end if;
    return true, G1, G2;
end function;

intrinsic HasDecomposition(G::SymGen) -> BoolElt, SeqEnum
    {Returns true and a sequence of genera which sum to G
    if there exists a lattice in the genus G which has an
    orthogonal decomposition.}
    n := Rank(G);
    require IsMaximal(G) : 
	"Argument must be a sequence of maximal local genera.";
    if n le 1 then return false, _; end if;
    bool, S1, S2 := HasDecompositionSequence(LocalGenera(G)); 
    if bool then
	_, G1 := IsConsistent(S1);
	_, G2 := IsConsistent(S2);
	return true, [G1, G2];
    end if;
    return false, _;
end intrinsic;

function HasDecompositionBinarySequence(S)
    return false, _, _;
end function;

function HasDecompositionSequence(S) 
    // PRE: A consistent sequence of local genera S.
    // POST: Returns true and consistent sequences 
    // S1 and S2 of local genera such that, for each i,
    // S1[i] + S2[i] = S[i]. 
    n := Rank(S[1]);
    if n le 1 then
	return false, _, _;
    elif n eq 2 then
	bool, S1, S2 := HasDecompositionBinarySequence(S);
	return bool, _, _;
    end if;
    c := 1;
    // find the candidate representation number
    for Gp in S do
	p := Prime(Gp);
	if p eq 2 and #Gp`JordanComponents eq 2 then
	    c *:= p;
	elif Rank(Gp`JordanComponents[1]) eq 1 then
	    c *:= p;
	end if;
    end for;
    // construct the splitting
    S1 := [];
    S2 := [];
    for i in [1..#S] do
	bool, S1[i], S2[i] := HasLocalSplitting(S[i],c);
	assert bool;
    end for;
    bool := IsConsistent(S1) and IsConsistent(S2); 
    if not bool then
	print "S1:"; S1;
	print "S2:"; S2;
    end if;
    return true, S1, S2;
end function;

