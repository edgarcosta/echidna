/**********************************************************
Compute period matrices for quartic CM fields (for Kohel)
Needs quartic.m to run (on my computer that is)
Calls the following functions in quartic.m - check names!

IsPrincipallyPolarizable
ComplexConjugation

Here is a test run:

> K := QuarticCMField([ 5, 33, 241 ]);
> OK := MaximalOrder(K);
> G, m := ClassGroup(K);
> I := m(G.1);
> CC := ComplexField(32);
> tau := SmallPeriodMatrix(I, CC);
> Im(tau);
[0.62378865204963409895804079673454 0.42030334507381554016759858201317]
[0.42030334507381554016759858201318 0.35304746722190080834057751774474]

Note the the imaginary part of tau is symmetric as it should be.

David Gruenewald -- 24th August 2007
**********************************************************/

//////////////////////////////////////////////////////////////////////////////
// Symplectic group Sp_4(ZZ).
//////////////////////////////////////////////////////////////////////////////

intrinsic SymplecticGroup(n::RngIntElt,ZZ::RngInt) -> AlgGrp
    {Symplectic group Sp(4,Z) defined in terms of generators, from 
    the GAP forum by Geoffrey Mess, UCLA, 1995.}
    require n eq 4 : "Argument 1 must be 4 :-).";
    G := GL(4,ZZ);
    tw1 := G![
	[ 1, 0, 0, 0 ],
	[ 1, 1, 0, 0 ],
	[ 0, 0, 1, 0 ],
	[ 0, 0, 0, 1 ] ];
    tw2 := G![
	[ 1,-1, 0, 0 ],
	[ 0, 1, 0, 0 ],
	[ 0, 0, 1, 0 ],
	[ 0, 0, 0, 1 ] ];
    tw3 := G![
	[1, 0, 0, 0 ],
	[1, 1,-1, 0 ],
	[0, 0, 1, 0 ],
	[-1, 0,1, 1 ] ];
    tw4 := G![
	[1, 0, 0, 0 ],
	[0, 1, 0, 0 ],
	[0, 0, 1, -1],
	[0, 0, 0,  1] ];
    tw5 := G![
	[1, 0, 0, 0 ],
	[0, 1, 0, 0 ],
	[0, 0, 1, 0 ],
	[0, 0, 1, 1 ] ];
    return sub< G | tw1, tw2, tw3, tw4, tw5 >;
end intrinsic;

/*

The symplectic group Sp(2g,Z) contains the elements

Translations:

  T = [ I S ] where S^t = S.
      [ 0 I ]

Rotations:

  R = [ U   0   ] where det(U) is a unit.
      [ 0 U^t^-1]

Semi-involutions:

  S = [ Q   I-Q ] where Q is diagonal with entries in {0,1}.
      [ Q-I  Q  ]

N.B. It would be nice to define a type for Sp(2g,R) in order to
extract the block matrices from U = [[A,B],[C,D]], and apply a
matrix to a given normalized tau in \H_g.

*/

//////////////////////////////////////////////////////////////////////////////
// Real and Imaginary parts of complex matrices.
//////////////////////////////////////////////////////////////////////////////

intrinsic Real(M::Mtrx[FldCom]) -> Mtrx
    {}
    CC := BaseRing(Parent(M));
    RR := RealField(Precision(CC));
    return Matrix(Ncols(M),[ Real(z) : z in Eltseq(M) ]);
end intrinsic;    

intrinsic Imaginary(M::Mtrx[FldCom]) -> Mtrx
    {}
    CC := BaseRing(Parent(M));
    RR := RealField(Precision(CC));
    return Matrix(Ncols(M),[ Im(z) : z in Eltseq(M) ]);
end intrinsic;    

//////////////////////////////////////////////////////////////////////////////
// Reduction of a "small" period matrix by symplectic transformations.
//////////////////////////////////////////////////////////////////////////////

function SymplecticReductionStep(tau)
    MatC := Parent(tau);
    g := Degree(MatC);
    // Translation reduction:
    T := MatrixAlgebra(IntegerRing(),2*g)!1;
    for i in [1..g] do
	if Abs(Re(tau[i,i])) gt 0.5 then
	    s := -Round(Re(tau[i,i]));
	    T[i,g+i] +:= s;
	    tau[i,i] +:= s;
	end if;
    end for;
    // Positive definite reduction:
    _, U := LLLGram((S + Transpose(S))/2) where S := Im(tau);
    tau := U*tau*Transpose(U); 
    T := DiagonalJoin(U,Transpose(U)^-1) * T;
    // Involution reduction:
    S := Parent(T)!0;
    one := MatC!1; tau1 := MatC!0; tau2 := MatC!0;
    for i in [1..g] do
	if Abs(tau[i,i]) gt 0.01^12 then
	    tau1[i] := tau[i];
	    tau2[i] := one[i];
	    S[i,i] := 1; S[g+i,g+i] := 1; 
	else
	    tau1[i] := one[i];
	    tau2[i] := -tau[i];
	    S[g+i,i] := -1; S[i,g+i] := 1; 
	end if;
    end for;
    T := S * T;
    tau := tau1 * tau2^-1;
    // Positive definite reduction:
    _, U := LLLGram((S + Transpose(S))/2) where S := Im(tau);
    tau := U*tau*Transpose(U); 
    T := DiagonalJoin(U,Transpose(U)^-1) * T;
    return tau, T;
end function;

intrinsic SymplecticReduction(tau::Mtrx[FldCom] : Al := "Wamelen") -> Mtrx
    {Reduction of the symplectic matrix with respect to Sp(2g,Z).}
    // Use van Wamelen's imlementation:
    if Al eq "Wamelen" then
	return To2DUpperHalfSpaceFundamentalDomian(tau);
    end if;
    g := Degree(Parent(tau));
    MatR := MatrixAlgebra(RealField(16),g);
    MatZ := MatrixAlgebra(IntegerRing(),2*g);
    U := MatZ!0;
    T := MatZ!1;
    i := 1; // sanity check...
    while U ne 1 do
	tau, U := SymplecticReductionStep(tau);
	if GetVerbose("FldCM") gt 0 then
	    print "Im:"; print MatR!Im(tau);
	    print "U:"; U;
	    print "det:", Determinant(MatR!Im(tau));
	end if;
	T := U*T;
	i +:= 1;
	assert i le 16; // some sanity...
    end while;
    return tau, T;
end intrinsic;

intrinsic RiemannMatrix(IK::RngOrdIdl,xi::RngElt) -> Mtrx
    {Given an ideal I in a quartic CM field, an purely imaginary element xi
    such that (xi) = I*Ibar*DK^-1, where DK is the different of OK, return
    a 2gx2g alternating matrix [Tr(xi^-1*x_i*\bar(x_j))] with respect to
    the basis (x_i) for IK.}
    OK := Order(IK);
    K := NumberField(OK);
    require IsCMField(K) : "Argument 1 must be an ideal in a CM field.";
    bool, xi := IsCoercible(K,xi);
    require bool : "Argument 2 must be coerible to the CM field of argument 1.";
    g := Degree(K) div 2;
    cc := ComplexConjugation(K);
    xi_inv := (K!xi)^-1;
    BK := [ K!x : x in Basis(IK) ];
    return Matrix(IntegerRing(),2*g,[ Trace(xi_inv*cc(x)*y) : x, y in BK ]);
end intrinsic;
    
intrinsic SmallPeriodMatrix(IK::RngOrdIdl,CC::FldCom :
    CMType := [], Reduction := false, Al := "Wamelen") -> Mtrx
    {Given an principally polarizable ideal I in a quartic CM field, find a
    purely imaginary element xi such that (xi) = I*Ibar*DK^-1, where DK is
    the different of OK, and return a gxg "small" period matrix tau.}
    K := NumberField(Order(IK));
    require IsCMField(K) : "Argument 1 must be an ideal in a CM field.";
    bool, xi := IsPrincipallyPolarizable(IK : Reduction := true);
    return SmallPeriodMatrix(IK,xi,CC :
	CMType := CMType, Reduction := Reduction, Al := Al);
end intrinsic;
    
intrinsic SmallPeriodMatrix(IK::RngOrdIdl,xi::RngElt,CC::FldCom :
    CMType := [], Reduction := false, Al := "Wamelen") -> Mtrx
    {Given an ideal I in a quartic CM field, an purely imaginary element xi
    such that (xi) = I*Ibar*DK^-1, where DK is the different of OK, return
    a gxg "small" period matrix tau.}
    OK := Order(IK);
    K := NumberField(OK);
    require IsCMField(K) : "Argument 1 must be an ideal in a CM field.";
    bool, xi := IsCoercible(K,xi);
    require bool : "Argument 2 must be coerible to the CM field of argument 1.";
    g := Degree(K) div 2;
    E := RiemannMatrix(IK,xi);
    BK := [ x : x in Basis(IK) ];
    // This is annoying: from V2.14-5 the function FrobeniusForm was 
    // renamed FrobeniusFormAlternating, and the name FrobeniusForm was
    // bound to an existing function RationalForm.
    x, y, z := GetVersion(); assert x eq 2;
    if y lt 14 or (y eq 14 and z lt 5) then
	FrobeniusMatrix := FrobeniusForm;
    else
	FrobeniusMatrix := FrobeniusFormAlternating;
    end if;
    D, C := FrobeniusMatrix(E);
    // assert D eq C * E * Transpose(C);
    if GetVerbose("FldCM") gt 0 then
	print "E:"; E;
	print "C:"; C;
    end if;
    I := [ 2*i-1 : i in [1..g] ];
    if #CMType eq 0 then
	CMType := [ 1 : i in [1..g] ];
    end if;
    for i in [1..g] do
	if CMType[i]*Im(Conjugate(xi,I[i])) gt 0 then
	    I[i] +:= 1;
	end if;
    end for;
    prec := Precision(CC);
    SetKantPrecision(K,2*prec);
    SetKantPrecision(OK,2*prec);
    FrobB := [ &+[ C[i,j]*BK[j] : j in [1..2*g] ] : i in [1..2*g] ];
    PerMat := Matrix(2*g,&cat[ [ Conjugate(x,I[i]) : x in FrobB ] : i in [1..g] ]);
    tau := Submatrix(PerMat,1,g+1,g,g)^-1*Submatrix(PerMat,1,1,g,g);
    if Reduction then
	tau := SymplecticReduction(tau : Al := Al);
    end if;
    return Matrix(g,ChangeUniverse(Eltseq(tau),CC));
end intrinsic;
    
/*
intrinsic BigPeriodMatrix(I::RngOrdIdl,CC::FldCom) -> Mtrx
    {Given a fractional ideal I in a quartic CM field return a big
    (2x4) period matrix if it is principally polarizable.}
    OK := Order(I);
    K := NumberField(OK);
    G, m := ClassGroup(K);
    ppble, xi := IsPrincipallyPolarizable(I : Reduction);
    require ppble : "This ideal class ain't principally polarizable!";
    SetKantPrecision(OK,Precision(CC));
    // Create CM type
    // there exists a CM-type such that Im(phi_i(xi^-1)) is positive for both embeddings 
    cmtypepos := [ k : k in [1..4] | Im(Conjugate(xi,k)) lt 0 ];
    cmtype := [ hom<K->CC | a :-> Conjugate(a,k)> : k in cmtypepos ];
    // Calculate Riemann forms, and symplectic bases of the ideals.
    // (taken from Daniel Vallieres' magma code from his Masters thesis) 
    xi_inv := xi^-1;
    K2 := CartesianProduct(K,K);
    conj := ComplexConjugation(K);
    riemannform := map<K2 -> Rationals() | x :-> Trace(xi_inv*conj(x[1])*x[2]) >;
    alpha := BasisMatrix(I);
    alpharow := RowSequence(alpha);
    E := Matrix(Rationals(),4,4,
	[riemannform(OK!alpharow[i],OK!alpharow[j]):i,j in [1..4]]);
    // don't know whether these next two lines are necessary but anyway 
    lcm := LCM([Denominator(x) :x in Eltseq(E)]);
    E := ChangeRing(lcm*E,Integers());
    fform, changeofbasis := FrobeniusForm(E);
    newbasis := changeofbasis*alpha;
    J := ideal<OK|newbasis>;
    bas := RowSequence(newbasis);
    BigPM := Matrix(CC,2,4,[cmtype[1](K!OK!b) : b in bas] cat [cmtype[2](K!OK!b) : b in bas]);
    return BigPM;
end intrinsic;

intrinsic SmallPeriodMatrix(I::RngOrdIdl,CC::FldCom) -> Mtrx
    {Given a fractional ideal in a quartic CM field return
    a small (2x2) period matrix if it is principally polarizable}
    bigPM := BigPeriodMatrix(I,CC);
    tau := Submatrix(bigPM,1,3,2,2)^-1*Submatrix(bigPM,1,1,2,2);
    return tau;
end intrinsic;
*/
