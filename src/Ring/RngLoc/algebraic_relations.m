/////////////////////////////////////////////////////////////////////////////
//                                                                         //
//   Algebraic Relations for Residue Class Rings                           //
//   Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu.au>              //
//                                                                         //
//   Distributed under the terms of the GNU General Public License (GPL)   //
//   Full text of the GPL is available at: http://www.gnu.org/licenses/    //
//                                                                         //
/////////////////////////////////////////////////////////////////////////////

declare verbose pAdicRelations, 2;

intrinsic RationalReconstruction(x::RngPadResElt) -> FldRatElt
    {}
    u := Integers()!x;
    p := Prime(Parent(x));
    m := Characteristic(Parent(x));
    M := LLL(Matrix(2,[u,1, m,0, 0,m]));
    while Valuation(M[1,2],p) gt 0 do
	m *:= p; 
	M := LLL(Matrix(2,[u,1, m,0, 0,m]));
    end while;
    return M[1,1]/M[1,2];
end intrinsic;

intrinsic RationalReconstruction(S::[RngPadResElt]) -> FldRatElt
    {}
    n := #S;
    p := Prime(Universe(S));
    m := Characteristic(Universe(S));
    S := [ Integers()!x : x in S ];
    I := IdentityMatrix(Integers(),n+1);
    M := LLL(VerticalJoin(Matrix(n+1,S cat [1]),m*I));
    return [ M[1,i]/M[1,n+1] : i in [1..n] ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function PolynomialRelations( pows, exps :
    LLLReduction := true, MaxRelations := 0, Scale := false)
    r := #exps[1]; 
    ZZ := Integers();
    P := PolynomialRing(ZZ,r : Global := true);
    xmons := [ &*[ P.j^e[j] : j in [1..r] ] : e in exps ];
    smons := [ &*[ pows[j][e[j]+1] : j in [1..r] ] : e in exps ];
    B := BasisMatrix(LinearRelations(smons : 
	LLLReduction := LLLReduction,
	MaxRelations := MaxRelations, Scale := Scale));
    t := #exps; s := Nrows(B);
    return [ P| &+[ B[i,j]*xmons[j] : j in [1..t] ] : i in [1..s] ];
end function;

////////////////////////////////////////////////////////////////////////
// Algebraic relations among a sequence of p-adic quotient ring elements
// (RngPadResElt). The three versions determine the shape of the bounds
// on the relation degrees.
////////////////////////////////////////////////////////////////////////

intrinsic AlgebraicRelations(
    S::[RngPadResElt],degs::[RngIntElt] : 
    LLLReduction := true, MaxRelations := 0, RingPrecision := 0,
    Scale := false) -> RngMPol
    {The ideal of relations between the elements of S, of coordinate
    degrees degs.}
    
    R := Universe(S);
    r := #S;
    s := 1;
    require #degs eq r : "Arguments must have the same length.";
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows := [ [ R!1 ] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	g1 := R!S[j];
	for i in [1..degs[j]] do
	    gi *:= g1;
	    Append(~pows[j],gi);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    exps := Reverse([ [ v[j] : j in [1..r] ] : v in Cdeg ]);
    return PolynomialRelations(pows,exps :
        LLLReduction := LLLReduction,
	MaxRelations := MaxRelations, Scale := Scale);
end intrinsic;

intrinsic AlgebraicRelations(
    S::[RngPadResElt],degs::[RngIntElt],tot::RngIntElt : 
    LLLReduction := true, MaxRelations := 0, RingPrecision := 0,
    Scale := false) -> RngMPol
    {The ideal of relations between the elements of S, of total degree
    at most tot and coordinate degrees degs.}
    
    R := Universe(S);
    r := #S;
    d := Degree(R);
    require #degs eq r : "Arguments must have the same length.";
    R := Universe(S);
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows := [ [Universe(S)|1] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	gg := R!S[j];
	for i in [1..degs[j]] do
	    gi *:= gg;
	    Append(~pows[j],gi);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := Reverse([ e : e in vecs | &+e le tot ]);
    return PolynomialRelations(pows,exps :
        LLLReduction := LLLReduction,
	MaxRelations := MaxRelations, Scale := Scale);
end intrinsic;

intrinsic AlgebraicRelations(
    S::[RngPadResElt],deg::RngIntElt : 
    LLLReduction := true, MaxRelations := 0, RingPrecision := 0,
    Scale := false) -> RngMPol
    {The ideal of relations between the elements of S, of degree at most deg.}
    
    R := Universe(S);
    r := #S;
    s := 1; 
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows := [ [ R!1 ] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	gg := R!S[j];
	for i in [1..deg] do
	    gi *:= gg;
	    Append(~pows[j],gi);
	end for;
    end for;
    Cdeg := CartesianPower({0..deg},r);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := Reverse([ e : e in vecs | &+e le deg ]);
    return PolynomialRelations(pows,exps :
        LLLReduction := LLLReduction,
	MaxRelations := MaxRelations, Scale := Scale);
end intrinsic;

////////////////////////////////////////////////////////////////////////
// Algebraic relations among a sequence of elements of an extension 
// of a p-adic quotient ring (RngPadResExtElt). The three versions
// determine the shape of the bounds on the relation degrees.
////////////////////////////////////////////////////////////////////////

intrinsic AlgebraicRelations(
    S::[RngPadResExtElt],degs::[RngIntElt] :
    LLLReduction := true, MaxRelations := 0, RingPrecision := 0,
    Scale := false) -> RngMPol
    {The ideal of relations between the elements of S, of coordinate
    degrees degs.}
    
    R := Universe(S);
    r := #S;
    s := Degree(R);
    require #degs eq r : "Arguments must have the same length.";
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows := [ [R!1] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	g1 := R!S[j];
	for i in [1..degs[j]] do
	    gi *:= g1;
	    Append(~pows[j],gi);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    exps := Reverse([ [ v[j] : j in [1..r] ] : v in Cdeg ]);
    return PolynomialRelations(pows,exps :
        LLLReduction := LLLReduction,
	MaxRelations := MaxRelations, Scale := Scale);
end intrinsic;

intrinsic AlgebraicRelations(
    S::[RngPadResExtElt],degs::[RngIntElt],tot::RngIntElt : 
    LLLReduction := true,
    MaxRelations := 0,
    RingPrecision := 0,
    Scale := false) -> RngMPol
    {The ideal of relations between the elements of S, of total degree
    at most tot and coordinate degrees degs.}
    
    R := Universe(S);
    r := #S;
    s := Degree(R);
    require #degs eq r : "Arguments must have the same length.";
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows := [ [R|1] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	gg := R!S[j];
	for i in [1..degs[j]] do
	    gi *:= gg;
	    Append(~pows[j],gi);
	end for;
    end for;
    Cdeg := CartesianProduct([{0..degs[j]}: j in [1..r]]);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := Reverse([ e : e in vecs | &+e le tot ]);
    return PolynomialRelations(pows,exps :
        LLLReduction := LLLReduction,
	MaxRelations := MaxRelations, Scale := Scale);
end intrinsic;

intrinsic AlgebraicRelations(S::[RngPadResExtElt],deg::RngIntElt :
    LLLReduction := true, MaxRelations := 0, RingPrecision := 0,
    Scale := false) -> RngMPol
    {The ideal of relations between the elements of S,
    of degree at most deg.}
    
    R := Universe(S);
    r := #S;
    s := Degree(R);
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows := [ [R|1] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	gg := R!S[j];
	for i in [1..deg] do
	    gi *:= gg;
	    Append(~pows[j],gi);
	end for;
    end for;
    Cdeg := CartesianPower({0..deg},r);
    vecs := [ [ v[j] : j in [1..r] ] : v in Cdeg ];
    exps := Reverse([ e : e in vecs | &+e le deg ]);
    return PolynomialRelations(pows,exps :
        LLLReduction := LLLReduction,
	MaxRelations := MaxRelations, Scale := Scale);
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic CommonAlgebraicRelations(
    X::[RngPadResElt],deg::RngIntElt : RingPrecision := 0) -> SeqEnum
    {The common polynomial relation satisfied by elements of S,
    of degree at most deg.}
    
    R := Universe(X);
    r := #X;
    d := Degree(R);
    require deg ge 1 : "Arguments 2 must be a positive integer.";
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows_seqs := [ [R|1] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	gg := R!X[j];
	for i in [1..deg] do
	    gi *:= gg;
	    Append(~pows_seqs[j],gi);
	end for;
    end for;
    L := &meet[ LinearRelations(pows) : pows in pows_seqs ];
    B := LLL(BasisMatrix(L));
    return [ Polynomial(Eltseq(B[i])) : i in [1..Nrows(B)] ];
end intrinsic;

intrinsic CommonAlgebraicRelations(
    X::[RngPadResExtElt],deg::RngIntElt : RingPrecision := 0) -> SeqEnum
    {The common polynomial relation satisfied by elements of X,
    of degree at most deg.}
    
    R := Universe(X);
    r := #X;
    d := Degree(R);
    require deg ge 1 : "Arguments 2 must be a positive integer.";
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	R := ChangePrecision(R,RingPrecision);
    end if;
    pows_seqs := [ [R|1] : i in [1..r] ];
    for j in [1..r] do
	gi := R!1;
	gg := R!X[j];
	for i in [1..deg] do
	    gi *:= gg;
	    Append(~pows_seqs[j],gi);
	end for;
    end for;
    L := &meet[ LinearRelations(pows) : pows in pows_seqs ];
    B := LLL(BasisMatrix(L));
    return [ Polynomial(Eltseq(B[i])) : i in [1..Nrows(B)] ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

intrinsic GaloisDescentAlgebraicRelation(
    X::[RngPadResElt], phi::Map :
    RingPrecision := 0, IntegralDenominator := true) -> RngUPol
    {}
    T := Universe(X);
    deg := #X;
    // Assume that the domain is an exact integral domain: 
    R := Domain(phi);
    F := FieldOfFractions(R);
    // The codomain should be a p-adic quotient ring.
    S := Codomain(phi);
    require Type(S) in {RngPadResExt, RngPadRes} :
	"Argument 2 must be a map to a p-adic quotient ring.";
    require deg ge 1 : "Argument 3 must be a positive integer.";
    if RingPrecision ne 0 then
	require RingPrecision gt 0 :
	    "Parameter RingPrecision must be positive.";
	T := ChangePrecision(R,RingPrecision);
    end if;
    // pows := [ F | ]; // 0-th term #X not taken in power to symmetric sums
    symm := [ F | ]; 
    dens := [ IntegerRing() | ];
    B0 := Basis(R); r := #B0;
    B1 := [ S | phi(xi) : xi in B0 ];
    x := PolynomialRing(T).1;
    symm_padic := Reverse(Eltseq(&*[ x - xi : xi in X ])[[1..deg]]);
    s := IntegralDenominator select 1 else r;
    for sj in symm_padic do
	if IntegralDenominator then
	    Lj := LinearRelations([-sj] cat B1 : LLLReduction);
	else
	    Lj := LinearRelations([-sj*x : x in B1] cat B1 : LLLReduction);
	end if;
	ij := 1; vj := Lj.ij;
	while vj[1] eq 0 and ij lt r+s do
	    ij +:= 1; vj := Lj.ij;
	end while;
	denj := IntegralDenominator select vj[1] else &+[ F | vj[i]*B0[i] : i in [1..r] ];
	numj := &+[ F | vj[i+s]*B0[i] : i in [1..r] ];
	Append(~symm,numj/denj);
	Append(~dens,denj);
    end for;
    x := PolynomialRing(F).1;
    f := x^deg + &+[ symm[i]*x^(deg-i) : i in [1..deg] ];
    if IntegralDenominator then
	f *:= LCM(dens);
    else
	require false : "Not implemented error.";
	// How, and for what rings, can we renormalize the projective point 
	// ( 1 : c_1 : ... : c_deg ) for c_i in the field of fractions F?
    end if;
    return PolynomialRing(R)!f;
end intrinsic;

intrinsic GaloisDescentAlgebraicRelation(
    X::[RngPadResExtElt], phi::Map : 
    RingPrecision := 0, IntegralDenominator := true) -> RngUPol
    {Given a sequence X = [x_1,...,x_n] of elements in some p-adic ring T over S, 
    a map phi: R -> S \subseteq T, find a common R-relation f(x_i) = 0 of degree
    deg satisfied by all x_i.  A polynomial f(x) in R[x] is returned.
    It is assumed that R has a finite basis of r elements over Z (returned by
    Basis(R)).  Moreover we assume that X represents a complete set of Gal(T/S)
    orbits of Gal(R/S)-conjugates in T/S.}

    d := #X; 
    T := Universe(X);
    t := Degree(T);
    deg := d*t;
    // Assume that the domain is an exact integral domain: 
    R := Domain(phi);
    F := FieldOfFractions(R);
    // The codomain should be a p-adic quotient ring.
    S := Codomain(phi);
    require Type(S) in {RngPadResExt, RngPadRes} :
	"Argument 2 must be a map to a p-adic quotient ring.";
    if RingPrecision ne 0 then
	require RingPrecision gt 0 : "Parameter RingPrecision must be positive.";
	T := ChangePrecision(R,RingPrecision);
    end if;
    // pows := [ F | ]; // 0-th term #X not taken in power to symmetric sums
    symm := [ F | ];
    dens := [ IntegerRing() | ];
    B0 := Basis(R); r := #B0;
    B1 := [ S | phi(xi) : xi in B0 ];
    x := PolynomialRing(T).1;
    Y := X;
    for j in [1..t-1] do
	Y := [ FrobeniusImage(xi) : xi in Y ];
	X cat:= Y;
    end for;
    f := &*[ x - xi : xi in X ];
    symm_padic := Reverse(Eltseq(f)[[1..deg]]);
    bool, symm_padic := CanChangeUniverse(symm_padic,S);
    require bool : "Symmetric products of orbits in argument 1 do not descend to codomain of argument 2.";
    // Change universe to S?
    s := IntegralDenominator select 1 else r;
    for sj in symm_padic do
	if IntegralDenominator then
	    Lj := LinearRelations([-sj] cat B1 : LLLReduction);
	else
	    Lj := LinearRelations([-sj*x : x in B1] cat B1 : LLLReduction);
	end if;
	ij := 1; vj := Lj.ij;
	while vj[1] eq 0 and ij lt r+s do
	    ij +:= 1; vj := Lj.ij;
	end while;
	denj := IntegralDenominator select vj[1] else &+[ F | vj[i]*B0[i] : i in [1..r] ];
	numj := &+[ F | vj[i+s]*B0[i] : i in [1..r] ];
	Append(~symm,numj/denj);
	Append(~dens,denj);
    end for;
    x := PolynomialRing(F).1;
    f := x^deg + &+[ symm[i]*x^(deg-i) : i in [1..deg] ];
    if IntegralDenominator then
	f *:= LCM(dens);
    else
	require false : "Not implemented error.";
	// How, and for what rings, can we renormalize the projective point 
	// ( 1 : c_1 : ... : c_deg ) for c_i in the field of fractions F?
    end if;
    return PolynomialRing(R)!f;
end intrinsic;

