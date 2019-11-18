//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// Univariate relations...
//////////////////////////////////////////////////////////////////////////////

intrinsic AlgebraicRelations(S::[FldFunRatUElt] :
    Labels := [], DomainRelations := [], CodomainRelations := [] ) -> RngMPol
    {}
    m := #S;
    R := Universe(S);
    n := Rank(R); // n = 1
    P := PolynomialRing(R,m+n);
    if #Labels eq 0 then
	AssignNames(~P,
	    [ "r" cat IntegerToString(i): i in [1..m]] cat 
	    [ Sprint(R.i) : i in [1..n] ]);
    else
	require #Labels eq m : "Invalid parameter Labels.";
	AssignNames(~P, Labels cat [ Sprint(R.i) : i in [1..n] ]);
    end if;
    vars := P.(m+1); // vars := [ P.j : j in [m+1..m+n] ];
    rels := [
	Evaluate(Denominator(S[i]),vars)*P.i -
	Evaluate(Numerator(S[i]),vars) : i in [1..m] ];
    if #DomainRelations ne 0 then
	Q := Universe(DomainRelations);
	require Type(Q) eq RngMPol : 
	    "Parameter DomainRelations must consist of polynomials.";
	require Rank(Q) eq n : 
	    "Rank of universe of DomainRelations " *
	    "must equal universe of argument 1.";
	rels cat:= [ f([ P.j : j in [m+1..m+n] ]) : f in Relations ];
    end if;
    J := EliminationIdeal(ideal< P | rels >,{P.i : i in [1..m]});
    P := PolynomialRing(R,m : Global);
    mons := [ P.i : i in [1..m] ] cat [ 0 : j in [1..n] ];
    I := ideal< P | [ Evaluate(f,mons) : f in Basis(J) ] >;
    return I;
end intrinsic;

intrinsic LinearRelations(S::[FldFunRatUElt] : Relations := [])
    -> ModTupFld
    {}
    for i in [1..#S] do
	den := Denominator(S[i]); 
	if den ne 1 then
	    S := [ den*f : f in S ];
	end if;
    end for;
    S := [ Numerator(f) : f in S ]; 
    if #Relations ne 0 then
	vprint RelationsJacG2 : "Putting functions in normal form.";
	P := Universe(Relations);
	require P eq Universe(S) : "Invalid Relations parameter.";
	I := ideal< Universe(S) | Relations >;
	S := [ NormalForm(f,I) : f in S ];
    end if;
    vprint RelationsJacG2 : "Extracting coefficients for matrix.";
    K := BaseRing(Universe(S));
    mons := &join[ SequenceToSet(Monomials(f)) : f in S ];
    vprint RelationsJacG2 : "Number of monomials:", #mons;
    vprintf RelationsJacG2 : "Matrix size %o x %o\n", #S, #mons;
    M := Matrix([ [ MonomialCoefficient(f,m) : m in mons ] : f in S ]);
    if GetVerbose("RelationsJacG2") ge 2 then
	for j in [1..#mons] do
	    "j =", j;
	    for i in [1..#S] do
		if M[i,j] ne 0 then
		    printf "M[%3o,%2o] = %o\n", i, j, M[i,j];
		end if;
	    end for;
	end for;
    end if;
    return Kernel(M);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Multivariate relations...
//////////////////////////////////////////////////////////////////////////////

intrinsic AlgebraicRelations(S::[FldFunRatMElt] :
    Labels := [],
    DomainRelations := [],
    CodomainRelations := [],
    UsePrimaryDecomposition := true
    ) -> RngMPol
    {}
    /*
    FF<u,v,w> := FunctionField(ZZ,3 : Global := false);
    B := [
        (u*v + u*w^2 + v*w^2)/w^2,
        (u^2*v + u*v^2 + u*v*w^2)/w^2,
        (u + v + w^2)/w,
        u*v/w
        ];
    assert B[2] eq B[3]*B[4];

    This is an example where the primary decomposition is required.
    */
    m := #S;
    R := Universe(S);
    n := Rank(R);
    P := PolynomialRing(R,m+n);
    if #Labels eq 0 then
	AssignNames(~P,
	    [ "r" cat IntegerToString(i): i in [1..m]] cat 
	    [ Sprint(R.i) : i in [1..n] ]);
    else
	require #Labels eq m : "Invalid parameter Labels.";
	AssignNames(~P, Labels cat [ Sprint(R.i) : i in [1..n] ]);
    end if;
    vars := [ P.j : j in [m+1..m+n] ];
    rels := [
	Evaluate(Denominator(S[i]),vars)*P.i -
	Evaluate(Numerator(S[i]),vars) : i in [1..m] ];
    if #DomainRelations ne 0 then
	Q := Universe(DomainRelations);
	require Type(Q) eq RngMPol : 
	    "Parameter DomainRelations must consist of polynomials.";
	require Rank(Q) eq n : 
	    "Rank of universe of DomainRelations " *
	    "must equal universe of argument 1.";
	rels cat:= [ f([ P.j : j in [m+1..m+n] ]) : f in DomainRelations ];
    end if;
    if UsePrimaryDecomposition then
	_, prms := PrimaryDecomposition(ideal< P | rels >);
    else
	prms := [ ideal< P | rels > ];
    end if;
    X := PolynomialRing(R,m : Global);
    mons := [ X.i : i in [1..m] ] cat [ 0 : j in [1..n] ];
    zero := true;
    for pp in prms do
	J := EliminationIdeal(pp, {P.i : i in [1..m]});
	I := ideal< X | [ Evaluate(f,mons) : f in Basis(J) ] >;
	if #Basis(I) eq 0 then continue; end if;
	if &and[ Evaluate(r,S) eq 0 : r in Basis(I) ] then
	    zero := false;
	    break;
	end if;
    end for;
    if zero then
	return ideal< X | [] >;
    end if;
    return I;
end intrinsic;

intrinsic LinearRelations(S::[FldFunRatMElt] : Relations := [])
    -> ModTupFld
    {}
    for i in [1..#S] do
	den := Denominator(S[i]); 
	if den ne 1 then
	    S := [ den*f : f in S ];
	end if;
    end for;
    S := [ Numerator(f) : f in S ]; 
    if #Relations ne 0 then
	vprint RelationsJacG2 : "Putting functions in normal form.";
	P := Universe(Relations);
	require P eq Universe(S) : "Invalid Relations parameter.";
	I := ideal< Universe(S) | Relations >;
	S := [ NormalForm(f,I) : f in S ];
    end if;
    vprint RelationsJacG2 : "Extracting coefficients for matrix.";
    K := BaseRing(Universe(S));
    mons := &join[ SequenceToSet(Monomials(f)) : f in S ];
    vprint RelationsJacG2 : "Number of monomials:", #mons;
    vprintf RelationsJacG2 : "Matrix size %o x %o\n", #S, #mons;
    M := Matrix([ [ MonomialCoefficient(f,m) : m in mons ] : f in S ]);
    if GetVerbose("RelationsJacG2") ge 2 then
	for j in [1..#mons] do
	    "j =", j;
	    for i in [1..#S] do
		if M[i,j] ne 0 then
		    printf "M[%3o,%2o] = %o\n", i, j, M[i,j];
		end if;
	    end for;
	end for;
    end if;
    return Kernel(M);
end intrinsic;

