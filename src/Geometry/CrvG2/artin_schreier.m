//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Multivariate Hensel lifting
//  Copyright (C) 2005 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
Created 13 June 2005
*/

intrinsic MultivariateNewtonLift(S::[RngMPolElt],X::[RngElt])
    -> SeqEnum
    {}
    P := Universe(S);
    R := Universe(X);
    n := Ngens(P);
    m := #S;
    require n eq m :
	"Argument 1 must consist of n polynomials in n unknowns.";
    require n eq #X : "Argument 2 has invalid length.";
    PhiX := Vector([ Evaluate(Phi,X) : Phi in S ]);
    while PhiX ne 0 do
	vX := Vector(X);
	DPhi := Matrix([
	    [ Evaluate(Derivative(Phi,i),X) : Phi in S ] : i in [1..n] ]);
	IPhi := DPhi^-1;
	X := Eltseq(vX - PhiX*IPhi);
    end while;
    return X;
end intrinsic;

/*
David Kohel, 13 June 2005
Artin-Schreier Root algorithm of Harley, c.f. Vercauteren, Thesis, 2003. 
*/

// RngPadElt's are not residue class rings so 'Expand' is used truncates
// the precision component.  Note that this class of rings includes both
// the p-adic rings and their extensions, while the quotient rings are
// differentiated by type.

intrinsic ArtinSchreierRoot(S::[RngPadResElt]) -> RngElt
    {}
    require #S eq 3 : "Argument must be a sequence of length 3.";
    R := Universe(S);
    N := Precision(R);
    p := ResidueCharacteristic(R);
    a, b, c := Explode(S);
    if N eq 1 then
	K := ResidueClassField(R);
	a0 := K!a; b0 := K!b; c0 := K!c;
	require a0 ne 0 : "First element of argument 1 must be a unit.";
	require b0 eq 0 :
	    "Second element of argument 1 must not be a unit.";
	y0 := -c0/a0;
	x1 := Expand(R!Root(y0,p));
	return x1;
    end if;
    N1 := N div 2;
    N2 := N - N1;
    R1 := ChangePrecision(R,N1);
    x1 := Expand(R!ArtinSchreierRoot([R1|a,b,c]));
    y1 := GaloisImage(x1,1);
    R2 := N2 gt N1 select ChangePrecision(R,N2) else R1;
    c1 := R2!Expand((a*y1 + b*x1 + c) div p^N1);
    dx := Expand(R!ArtinSchreierRoot([R2|a,b,c1]));
    return x1 + p^N1*dx; 
end intrinsic;

intrinsic ArtinSchreierRoot(S::[RngPadResExtElt]) -> RngElt
    {}
    require #S eq 3 : "Argument must be a sequence of length 3.";
    R := Universe(S);
    N := Precision(R);
    p := ResidueCharacteristic(R);
    a, b, c := Explode(S);
    if N eq 1 then
	K := ResidueClassField(R);
	a0 := K!a; b0 := K!b; c0 := K!c;
	require a0 ne 0 : "First element of argument 1 must be a unit.";
	require b0 eq 0 :
	    "Second element of argument 1 must not be a unit.";
	y0 := -c0/a0;
	x1 := R!Root(y0,p);
	return x1;
    end if;
    N1 := N div 2;
    N2 := N - N1;
    R1 := ChangePrecision(R,N1);
    x1 := R!ArtinSchreierRoot([R1|a,b,c]);
    y1 := GaloisImage(x1,1);
    R2 := N2 gt N1 select ChangePrecision(R,N2) else R1;
    c1 := R2!((a*y1 + b*x1 + c) div p^N1);
    dx := R!ArtinSchreierRoot([R2|a,b,c1]);
    return x1 + p^N1*dx; 
end intrinsic;

/*
David Kohel, 19 June 2005
Multivariate version of Artin-Schreier Root algorithm
*/

intrinsic ArtinSchreierRoots(
    A::AlgMatElt,B::AlgMatElt,C::ModTupRngElt,r::RngIntElt) -> SeqEnum
    {A solution to YA + XB + C = 0 where Y is the r-th power
    Frobenius image of X.}
    MatR := Parent(A);
    VecR := Parent(C);
    R := BaseRing(MatR);
    require R eq BaseRing(VecR) and R eq BaseRing(Parent(B)) : 
	"Arguments must be defined over the same base ring.";
    require Type(R) in {RngPadRes,RngPadResExt} : 
	"Arguments must be defined over a p-adic ring.";
    N := Precision(R);
    p := ResidueCharacteristic(R);
    q := p^r;
    n := Degree(MatR);
    if N eq 1 then
	K<w> := ResidueClassField(R);
	MatK := MatrixAlgebra(K,n);
	VecK := RSpace(K,n);
	A0 := MatK!A; B0 := MatK!B; C0 := VecK!C;
	require Determinant(A0) ne 0 :
	    "First element of argument 1 must be invertible.";
	if B0 eq 0 then
	    Y0 := -C0*A0^-1;
	    X0 := VecK![ Root(y0,q) : y0 in Eltseq(Y0) ];
	    return [ VecR!X0 ];
	else // This is more expensive if i > 1.
	    PK := PolynomialRing(K,n);
	    MatK := MatrixAlgebra(PK,n);
	    VecPK := RSpace(PK,n);
	    X0 := VecPK![ PK.i : i in [1..n] ];
	    Y0 := VecPK![ PK.i^q : i in [1..n] ];
	    AY := Y0*MatK!A0;
	    BY := X0*MatK!B0;
	    CY := VecPK!C0;
	    I0 := ideal< PK | Eltseq(AY+BY+CY) >;
	    V0 := Variety(I0);
	    //print "Number of rational points:", #V0;
	    return [ VecR | [ dt[i] : i in [1..n] ] : dt in V0 ];
	end if;
    end if;
    N1 := N div 2;
    N2 := N - N1;
    R1 := ChangePrecision(R,N1);
    MatR1 := MatrixAlgebra(R1,n);
    VecR1 := RSpace(R1,n);
    X1sols := [ VecR!X1 : X1 in
	ArtinSchreierRoots(MatR1!A,MatR1!B,VecR1!C,r) ];
    // print "N1:", N1;
    // zz := Y1*MatR1!A + VecR1!X1*MatR1!B + VecR1!C
    // where Y1 := VecR1![ R1!GaloisImage(x,r) : x in Eltseq(X1) ];
    // "Val1:", [ Valuation(z) : z in Eltseq(zz) ];
    Y1sols := [
	VecR![ GaloisImage(x1,r) : x1 in Eltseq(X1) ] : X1 in X1sols ];
    R2 := N2 gt N1 select ChangePrecision(R,N2) else R1;
    MatR2 := N2 gt N1 select MatrixAlgebra(R2,n) else MatR1;
    VecR2 := N2 gt N1 select RSpace(R2,n) else VecR1;
    C1sols := [ VecR2![ c div p^N1 :
	c in Eltseq(Y1sols[i]*A + X1sols[i]*B + C) ] : i in [1..#X1sols] ];
    DXsols := [ [ VecR!DX : DX in ArtinSchreierRoots(
	MatR2!A,MatR2!B,C1sols[i],r) ] : i in [1..#C1sols] ];
    // print "N2:", N1;
    // zz := VecR2!DY*MatR2!A + VecR2!DX*MatR2!B + C1
    // where DY := VecR2![ R!GaloisImage(x,r) : x in Eltseq(DX) ];
    // "Val2:", [ Valuation(z) : z in Eltseq(zz) ];
    // print "N1+N2:", N1+N2;
    // zz := Y*A + X*B + C
    // where Y := VecR![ R!GaloisImage(x,r) : x in Eltseq(X) ]
    // where X := X1 + p^N1*DX;
    // "Vals:", [ Valuation(z) : z in Eltseq(zz) ];
    return &cat[
	[ X1sols[i] + p^N1*DX : DX in DXsols[i] ] : i in [1..#X1sols] ];
end intrinsic;

intrinsic ArtinSchreierRoot(A::AlgMatElt,B::AlgMatElt,C::ModTupRngElt) -> ModTupRngElt
    {}
    return ArtinSchreierRoot(A,B,C,1);
end intrinsic;

intrinsic ArtinSchreierRoot(
    A::AlgMatElt,B::AlgMatElt,C::ModTupRngElt,r::RngIntElt) -> ModTupRngElt
    {}
    MatR := Parent(A);
    VecR := Parent(C);
    R := BaseRing(MatR);
    R := BaseRing(MatR);
    require R eq BaseRing(VecR) and R eq BaseRing(Parent(B)) : 
	"Arguments must be defined over the same base ring.";
    require Type(R) in {RngPadRes,RngPadResExt} : 
	"Arguments must be defined over a p-adic ring.";
    N := Precision(R);
    p := ResidueCharacteristic(R);
    q := p^r;
    require R eq BaseRing(VecR) :
	"Arguments 1 and 2 have incompatible rings.";
    n := Degree(MatR);
    require n eq Rank(VecR) :
	"Arguments 1 and 2 have incompatible degrees.";
    if N eq 1 then
	K<w> := ResidueClassField(R);
	MatK := MatrixAlgebra(K,n);
	VecK := RSpace(K,n);
	A0 := MatK!A; B0 := MatK!B; C0 := VecK!C;
	require Determinant(A0) ne 0 :
	    "First element of argument 1 must be invertible.";
	if B0 eq 0 then
	    Y0 := -C0*A0^-1;
	    X0 := VecK![ Root(y0,q) : y0 in Eltseq(Y0) ];
	    return VecR!X0;
	else
	    PK := PolynomialRing(K,n);
	    MatK := MatrixAlgebra(PK,n);
	    VecPK := RSpace(PK,n);
	    X0 := VecPK![ PK.i : i in [1..n] ];
	    Y0 := VecPK![ PK.i^q : i in [1..n] ];
	    AY := Y0*MatK!A0;
	    BY := X0*MatK!B0;
	    CY := VecPK!C0;
	    I0 := ideal< PK | Eltseq(AY+BY+CY) >;
	    V0 := Variety(I0);
	    print "Number of rational points:", #V0;
	    print "Rational points:"; V0;
	    assert #V0 gt 0;
	    return VecR![ dt[i] : i in [1..n] ] where dt := Random(V0);
	end if;
    end if;
    N1 := N div 2;
    N2 := N - N1;
    R1 := ChangePrecision(R,N1);
    MatR1 := MatrixAlgebra(R1,n);
    VecR1 := RSpace(R1,n);
    X1 := VecR!ArtinSchreierRoot(MatR1!A,MatR1!B,VecR1!C,r);
    // print "N1:", N1;
    // zz := Y1*MatR1!A + VecR1!X1*MatR1!B + VecR1!C
    // where Y1 := VecR1![ R1!GaloisImage(x,r) : x in Eltseq(X1) ];
    // "Val1:", [ Valuation(z) : z in Eltseq(zz) ];
    Y1 := VecR![ GaloisImage(x1,r) : x1 in Eltseq(X1) ];
    R2 := N2 gt N1 select ChangePrecision(R,N2) else R1;
    MatR2 := N2 gt N1 select MatrixAlgebra(R2,n) else MatR1;
    VecR2 := N2 gt N1 select RSpace(R2,n) else VecR1;
    C1 := VecR2![ c div p^N1 : c in Eltseq(Y1*A + X1*B + C) ];
    DX := VecR!ArtinSchreierRoot(MatR2!A,MatR2!B,C1,r);
    // print "N2:", N1;
    // zz := VecR2!DY*MatR2!A + VecR2!DX*MatR2!B + C1
    // where DY := VecR2![ R!GaloisImage(x,r) : x in Eltseq(DX) ];
    // "Val2:", [ Valuation(z) : z in Eltseq(zz) ];
    // print "N1+N2:", N1+N2;
    // zz := Y*A + X*B + C
    // where Y := VecR![ R!GaloisImage(x,r) : x in Eltseq(X) ]
    // where X := X1 + p^N1*DX;
    // "Vals:", [ Valuation(z) : z in Eltseq(zz) ];
    return X1 + p^N1*DX;
end intrinsic;

/*

PXY<T0,T1,T2,U,V,W> := PolynomialRing(ZZ,6);
Phi := [
    U^2 - 2*T2*U + T1*T2 - T1 + T2,
    -V^2 + 2*T2*V - T0*T2,
    (T0 - T1 - 1)*W^2 + 2*T1*W - T0*T1 ];
DxPhi := Matrix([[0,-T2,W^2-T1],[T2-1,0,-W^2+2*W-T0],[-2*U+T1+1,2*V-T0,0]]);
DyPhi := DiagonalMatrix([ 2*U-2*T2, -2*V+2*T2, 2*(T0-T1-1)*W + 2*T1 ]);
KXY<T0,T1,T2,U,V,W> := FieldOfFractions(PXY);
U2 := U; U1 := 2*T2-U;
V0 := V; V2 := 2*T2-V;
W0 := W; W1 := -2*T1/(T0-T1-1)-W;
TT := [ 2*T2, 2*T2, -2*T1/(T0-T1-1) ];
fX := function(X,T)
   X0,X1,X2 := Explode(X);
   return [ (X1-X2)*(Y-X0)/((X1-X0)*(Y-X2)) : Y in T ];
end function;
Psi := [
    (U1-V2)*(U2-V0)/((U1-V0)*(U2-V2)),
    (U1-V2)*(W1-V0)/((U1-V0)*(W1-V2)),
    (U1-V2)*(W0-V0)/((U1-V0)*(W0-V2))
    ];
assert Psi eq fX([V0,U1,V2],[U2,W1,W0]);
PsiAll := [
    fX([V0,U1,V2],[U2,W1,W0]),
    fX([V0,U1,U2],[V2,W1,W0]),
    fX([V0,W1,V2],[U2,U1,W0]),
    fX([V0,W1,U2],[V2,U1,W0]),
    fX([W0,U1,V2],[U2,W1,V0]),
    fX([W0,U1,U2],[V2,W1,V0]),
    fX([W0,W1,V2],[U2,U1,V0]),
    fX([W0,W1,U2],[V2,U1,V0])
];
DxPsi := Matrix([ [ Derivative(S,i) : S in Psi ] : i in [1..3] ]);
DyPsi := Matrix([ [ Derivative(S,i) : S in Psi ] : i in [4..6] ]);

*/

