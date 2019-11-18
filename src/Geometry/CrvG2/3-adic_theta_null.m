//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Canonical Lifts of 3-Adic Theta Null Points                             //
//                                                                          //
//  Copyright (C) 2006 David Lubicz <david.lubicz@math.univ-rennes1.fr>     //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu.au>                //
//  Copyright (C) 2006 Robert Carls <carls@maths.usyd.edu.au>               //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
We implement an algorithm for canonical lifting of ordinary theta null points.

// Example 1. Maps between theta null points.
p := 101;
FF := FiniteField(p);
KK<s> := FiniteField(p,4);
yy := [ KK | Random(FF) : i in [1..4] ]; 
xx := Level4ThetaNullPointFromLevel2ThetaNullPoint(yy : Normalize);
R := pAdicQuotientRing(p,16);
S := UnramifiedExtension(R,4); Embed(KK,ResidueClassField(S));
XX := ChangeUniverse(xx,S);
YY := Level4ThetaNullPointToIsogenousLevel2ThetaNullPoint(XX);
WW := Level4ThetaNullPointFromIsogenousLevel2ThetaNullPointHensel(YY,XX);
[ Valuation(XX[i]-WW[i]) : i in [1..10] ];

// Example 2. Verification of formulae for 2-theta null points to Rosenhain:
F<y00,y01,y10,y11> := FunctionField(ZZ,4);
yy := [y00,y01,y10,y11];
ee := Level2ThetaNullPointToRosenhainInvariants(yy);
Level2ThetaNullPointFromRosenhainInvariants(ee);

// Example 3. A. Canonical lifting in characteristic 3.
prec := 1024;
FF<t> := FiniteField(3,5);
PF<x> := PolynomialRing(FF);
f := 52*x^5 - 156*x^4 + 208*x^3 - 156*x^2 + 64*x - 11;
C := HyperellipticCurve(f);
ee := RosenhainInvariants(C);
KK<s> := FiniteField(3,20);
ee1 := ChangeUniverse(ee,KK);
yy1 := Level2ThetaNullPointFromRosenhainInvariants(ee1);
xx1 := Level4ThetaNullPointFromLevel2ThetaNullPoint(yy1);
XX1 := CanonicalLiftLevel4ThetaNullPoint(xx1,prec);
YY1 := Level4ThetaNullPointToLevel2ThetaNullPoint(XX1);
EE1 := Level2ThetaNullPointToRosenhainInvariants(YY1);
JJ1 := RosenhainToAbsoluteIgusaInvariants(EE1);
// Reconstruct the absolute Igusa invariants of original curve:
[ AlgebraicRelations([JJ1[i]],1)[1] : i in [1..10] ];

// Example 3. A (continued) 
// Compute invariants of (2,2)-isogenous "+1" Jacobian:
YY2 := XX1[[1..4]];
EE2 := Level2ThetaNullPointToRosenhainInvariants(YY2);
JJ2 := RosenhainToAbsoluteIgusaInvariants(EE2);
// Reconstruct the absolute Igusa invariants of (2,2)-isogenous +1 curve:
[ AlgebraicRelations([JJ2[i]],10)[1] : i in [1,2,4] ];
// Compute invariants of (2,2)-isogenous "-1" Jacobian:
XX0 := Level4ThetaNullPointFromLevel2ThetaNullPoint(YY1);
YY0 := Level4ThetaNullPointToLevel2ThetaNullPoint(XX0);
EE0 := Level2ThetaNullPointToRosenhainInvariants(YY0);
JJ0 := RosenhainToAbsoluteIgusaInvariants(EE0);
// Reconstruct the absolute Igusa invariants of (2,2)-isogenous -1 curve:
[ AlgebraicRelations([JJ0[i]],5)[1] : i in [1,2,4] ];

// Example 3. B.
// Note that the 4-theta structure XX1 can be defined
// over a 3-adic ring of degree 10, not 20, while the (2,2)-isogenous
// 4-theta structures XX0 and XX2 require the degree 20 extension.
prec := 256;
FF<t> := FiniteField(3,5);
PF<x> := PolynomialRing(FF);
f := 52*x^5 - 156*x^4 + 208*x^3 - 156*x^2 + 64*x - 11;
C := HyperellipticCurve(f);
ee := RosenhainInvariants(C);
KK<t> := FiniteField(3,10);
ee1 := ChangeUniverse(ee,KK);
yy1 := Level2ThetaNullPointFromRosenhainInvariants(ee1);
xx1 := Level4ThetaNullPointFromLevel2ThetaNullPoint(yy1);
XX1 := CanonicalLiftLevel4ThetaNullPoint(xx1,prec);
YY1 := Level4ThetaNullPointToLevel2ThetaNullPoint(XX1);
EE1 := Level2ThetaNullPointToRosenhainInvariants(YY1);
JJ1 := RosenhainToAbsoluteIgusaInvariants(EE1);
// Reconstruct the absolute Igusa invariants of original curve:
[ AlgebraicRelations([JJ1[i]],1)[1] : i in [1..10] ];
// Reconstruct the Rosenhain invariants of original curve:
[ AlgebraicRelations([EE1[i]],20)[1] : i in [1..3] ];

// Example 4.
FF<t> := FiniteField(3,3);
Pnts := EnumerateOrdinaryLevel2ThetaNullPoints(FF);
tt := [ Level4ThetaNullPointFromLevel2ThetaNullPoint(tt) : tt in Pnts |
    ExistsLevel4ThetaNullPointFromLevel2ThetaNullPoint(tt) ][1];
TT := CanonicalLiftLevel4ThetaNullPoint(tt,1024);
YY := Level4ThetaNullPointToLevel2ThetaNullPoint(TT);
EE := Level2ThetaNullPointToRosenhainInvariants(YY);
JJ := RosenhainToAbsoluteIgusaInvariants(EE);
[ AlgebraicRelations(JJ[[1,2,4]],I)[1] : I in [[3,0,0],[0,3,0],[0,0,3]] ];

*/

/////////////////////////////////////////////////////////////////////////

function ProjectiveNormalisation(v)
    bool, u1 := IsInvertible(v[1]); assert bool;
    return [ ci * u1 : ci in v ];
end function;

//////////////////////////////////////////////////////////////////////////////
// Maps between different theta moduli spaces
//////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
// Modular Equations
///////////////////////////////////////////////////////////////////////////////

function RiemannRelations(P)
    x00,x02,x20,x22,x01,x21,x10,x12,x11,x13 := Explode([ P.i : i in [1..10] ]);
    return [
	(x00^2+x02^2+x20^2+x22^2)*(x00*x02+x20*x22) - 2*(x01^2+x21^2)^2,
	(x00^2+x02^2+x20^2+x22^2)*(x00*x20+x02*x22) - 2*(x10^2+x12^2)^2,
	(x00^2+x02^2+x20^2+x22^2)*(x00*x22+x20*x02) - 2*(x11^2+x13^2)^2,
	(x00*x20+x02*x22)*(x00*x22+x02*x20) - 4*x01^2*x21^2,
	(x00*x02+x20*x22)*(x00*x22+x02*x20) - 4*x10^2*x12^2,
	(x00*x02+x20*x22)*(x00*x20+x02*x22) - 4*x11^2*x13^2,
	(x00^2+x02^2+x20^2+x22^2)*x13*x11 - (x12^2+x10^2)*(x01^2+x21^2),
	(x00^2+x02^2+x20^2+x22^2)*x01*x21 - (x12^2+x10^2)*(x11^2+x13^2),
	(x00^2+x02^2+x20^2+x22^2)*x10*x12 - (x01^2+x21^2)*(x11^2+x13^2),
	(x02*x20+x00*x22)*x11*x13 - 2*x01*x10*x21*x12,
	(x02*x20+x00*x22)*(x01^2+x21^2) - 2*x10*x12*(x11^2+x13^2),
	(x02*x20+x00*x22)*(x10^2+x12^2) - 2*x01*x21*(x11^2+x13^2),
	(x00*x20+x22*x02)*x10*x12 - 2*x11*x13*x21*x01,
	(x00*x20+x22*x02)*(x13^2+x11^2) - 2*(x10^2+x12^2)*x21*x01,
	(x00*x20+x22*x02)*(x21^2+x01^2) - 2*(x10^2+x12^2)*x11*x13,
	(x00*x02+x20*x22)*x21*x01 - 2*x11*x13*x10*x12,
	(x00*x02+x20*x22)*(x12^2+x10^2) - 2*x11*x13*(x01^2+x21^2),
	(x00*x02+x20*x22)*(x11^2+x13^2) - 2*x10*x12*(x01^2+x21^2),
	x01*x21*(x01^2+x21^2) - x10*x12*(x10^2+x12^2),
	x01*x21*(x01^2+x21^2) - x11*x13*(x11^2+x13^2) ];
end function;

function CorrespondenceRelations(P,prime)
    assert prime eq 3;
    x00,x02,x20,x22,x01,x21,x10,x12,x11,x13 := Explode([ P.i : i in [1..10] ]);
    y00,y02,y20,y22,y01,y21,y10,y12,y11,y13 := Explode([ P.i : i in [11..20] ]);
    return [
	(x00*y02+x02*y00+x20*y22+x22*y20)-2*(x01*y01+x21*y21),
	(x00*y20+x20*y00+x02*y22+x22*y02)-2*(x10*y10+x12*y12),
	(x00*y22+x22*y00+x02*y20+x20*y02)-2*(x13*y13+x11*y11) ];
end function;

///////////////////////////////////////////////////////////////////////
// Some helpful functions
///////////////////////////////////////////////////////////////////////

function MinValuation(v)
    return Min([ Valuation(c) : c in v ]);
end function;

function DivSequence(x,n)
    return [ c div n : c in x ];
end function;

function BaseChangeVector(x,S)
    return Vector([ S!c : c in Eltseq(x) ]);
end function;

function BaseChangeMatrix(M,S)
    return Matrix([[ S!M[i,j] : j in [1..Ncols(M)]] : i in [1..Nrows(M)]]);
end function;

function FrobeniusSequence(x, k)
    return [ GaloisImage(c,k) : c in x ];
end function;

function FrobeniusVector(x, k)
    return Vector([ GaloisImage(c,k) : c in Eltseq(x) ]);
end function;

function FrobeniusMatrix(A, k)
    R := BaseRing(Parent(A));
    case Category(R):
    when FldFin:
	p := Characteristic(R);
	return Parent(A)![ c^(p^k) : c in Eltseq(A) ];
    when RngPadResExt:
	return Parent(A)![ GaloisImage(c,k) : c in Eltseq(A) ];
    end case;
    assert false;
end function;

function EvaluateMatrix(M,x)
    c := Eltseq(x);
    return Matrix([ [
	Evaluate(M[i,j],c) : j in [1..Ncols(M)] ] : i in [1..Nrows(M)] ]);
end function;

////////////////////////////////////////////////////////////////////////
// The definition of Phi and derivatives
//////////////////////////////////////////////////////////////////////

function Phi(CorrEQs,x,y)
    return [ Evaluate(f,x cat y) : f in CorrEQs ];
end function;

function DPhi0(DCorrEQs,x,y)
    return EvaluateMatrix(DCorrEQs,x cat y);
end function;

function DerivativeLocalInverse(x,DRiemEQs)
    D := EvaluateMatrix(DRiemEQs,x);
    DPsi1 := ColumnSubmatrix(D,1,3);
    DPsi2 := ColumnSubmatrix(D,4,6);
    E, T := EchelonForm(DPsi2); assert RowSubmatrix(E,1,6) eq 1;
    U := IdentityMatrix(Universe(x),3);
    Dg := -RowSubmatrix(T,6)*DPsi1;
    return VerticalJoin(U,Dg);
end function;

/////////////////////////////////////////////////////////////////////////////////
// The lifting algorithm
/////////////////////////////////////////////////////////////////////////////////

intrinsic ArtinSchreierRootRobert(A::Mtrx,c::ModTupRngElt) -> ModTupRngElt
    {This function solves an equation of the form x^sigma + A*x + c = 0 for
    a vector x, where the matrix A must equal zero over the residue field.}
    S0 := BaseRing(Parent(A));
    V := Parent(c); N := Rank(V);
    require S0 eq BaseRing(V) : "Arguments have incompatible rings.";
    require N eq Ncols(A) and N eq Nrows(A) : "Arguments are incompatible.";
    prec := Precision(S0);
    if prec eq 1 then
	return FrobeniusVector(-c,-1);
    end if;
    r := (prec+1) div 2;
    S1 := ChangePrecision(S0,r);
    A1 := BaseChangeMatrix(A,S1);
    c1 := BaseChangeVector(c,S1);
    x1 := BaseChangeVector(ArtinSchreierRootRobert(A1,c1),S0);
    y1 := FrobeniusVector(x1,1);
    char := Characteristic(ResidueClassField(S0));
    d1 := DivSequence(Eltseq(y1 + x1*Transpose(A) + c),char^r);
    c2 := Vector(ChangeUniverse(d1,S1));
    delta := BaseChangeVector(ArtinSchreierRootRobert(A1,c2),S0);
    return x1 + char^r * delta;
end intrinsic;

function NewtonThetaLift(Xl4,CorrEQs,DCorrEQs,RiemEQs,DRiemEQs)
    SS := Universe(Xl4);
    prec := Precision(SS);
    if prec eq 1 then return Xl4; end if;
    KK := ResidueClassField(SS); char := Characteristic(KK);
    Xl4_prev := Xl4;
    Yl4_prev := FrobeniusSequence(Xl4_prev,1);
    Xl2_prev := Level4ThetaNullPointToIsogenousLevel2ThetaNullPoint(Xl4);
    
    r := (prec+1) div 2;
    
    vprintf CanonicalLift : "REDUCING TO LOWER PRECISION: %o\n", r;
    
    S1 := ChangePrecision(SS,r); AssignNames(~S1,["t"]);
    Xl4_half_S1 := ChangeUniverse(Xl4_prev,S1);
    Xl4_half_S1 := NewtonThetaLift(Xl4_half_S1,CorrEQs,DCorrEQs,RiemEQs,DRiemEQs);
    Yl4_half_S1 := FrobeniusSequence(Xl4_half_S1,1);
    vprintf CanonicalLift : "LIFTED HALFWAY TO PRECISION: %o\n", r;
    
    Xl4_half := Level4ThetaNullPointFromIsogenousLevel2ThetaNullPointHensel(
	ChangeUniverse(Xl4_half_S1,SS),Xl4_prev);
    Yl4_half := FrobeniusSequence(Xl4_half,1);
    
    DX := DerivativeLocalInverse(Xl4_half_S1,DRiemEQs);
    DY := FrobeniusMatrix(DX,1);

    tyme := Cputime();
    MatS := MatrixAlgebra(S1,3);
    DCorrEQsX := ColumnSubmatrix(DCorrEQs,1,9);
    A := MatS!(EvaluateMatrix(DCorrEQsX,Xl4_half_S1 cat Yl4_half_S1) * DX);
    DCorrEQsY := ColumnSubmatrix(DCorrEQs,10,9);
    B := MatS!(EvaluateMatrix(DCorrEQsY,Xl4_half_S1 cat Yl4_half_S1) * DY);
    vprint CanonicalLift, 2 : "A,B-Matrix computations:", Cputime(tyme);
    
    V := Vector(ChangeUniverse(
	DivSequence(Phi(CorrEQs,Xl4_half,Yl4_half),char^r),S1));
    
    assert BaseChangeMatrix(A,KK) eq ZeroMatrix(KK,3,3);
    
    bool, M := IsInvertible(B); assert bool;
    delta := BaseChangeVector(ArtinSchreierRootRobert(M*A,V*Transpose(M)),SS);
    
    if GetVerbose("CanonicalLift") ge 2 then
	tyme := Cputime();
	X := EvaluateMatrix(DRiemEQs,Xl4_half_S1);
	assert &and[ X[i]*DX eq 0 : i in [1..Nrows(DX)] ];
	long := false; // false = faster, but keep to check consistency
	if long then
	    d_x := BaseChangeVector(Vector(delta) * Transpose(DX),S1);
	    d_y := FrobeniusVector(d_x,1);
	    DCorrX := EvaluateMatrix(DCorrEQsX,Xl4_half_S1 cat Yl4_half_S1);
	    DCorrY := EvaluateMatrix(DCorrEQsY,Xl4_half_S1 cat Yl4_half_S1);
	    assert BaseChangeVector(
		d_y*Transpose(DCorrY) + d_x*Transpose(DCorrX) + V,S1) eq 0;
	else
	    d_x := BaseChangeVector(delta,S1);
	    d_y := FrobeniusVector(d_x,1);
	    B1 := BaseChangeMatrix(B,S1);
	    A1 := BaseChangeMatrix(A,S1);
	    V1 := BaseChangeVector(V,S1); 
	    assert Vector(d_y)*Transpose(B1) + Vector(d_x)*Transpose(A1) + V1 eq 0;
	end if;
	vprint CanonicalLift, 2 : "Checking time #1:", Cputime(tyme);
    end if;
    
    tyme := Cputime();
    Xl2_half := Level4ThetaNullPointToIsogenousLevel2ThetaNullPoint(Xl4_half);
    Xl2_full := Eltseq(Vector(Xl2_half) + char^r * Vector([ SS!0 ] cat Eltseq(delta)));
    Xl4_full := Level4ThetaNullPointFromIsogenousLevel2ThetaNullPointHensel(Xl2_full,Xl4_half);
    assert Xl2_full eq Level4ThetaNullPointToIsogenousLevel2ThetaNullPoint(Xl4_full);
    vprint CanonicalLift, 2 : "Full lifted computation:", Cputime(tyme);
    // Alternatively we could compute Xl4_full as follows:
    tyme := Cputime();
    full_delta := [ S1!0 ] cat Eltseq(Vector(delta) * Transpose(DX));
    assert Xl4_full eq Eltseq(Vector(Xl4_half) + char^r * Vector(ChangeUniverse(full_delta,SS)));
    vprint CanonicalLift, 2 : "Alternative computation:", Cputime(tyme);
    
    if GetVerbose("CanonicalLift") ge 2 then
	tyme := Cputime();
	Yl4_prev := FrobeniusSequence(Xl4_prev,1);
	Yl4_full := FrobeniusSequence(Xl4_full,1);
	v_full := Vector([ Evaluate(f,Eltseq(Xl4_full)) : f in RiemEQs ]);
	u_full := Phi(CorrEQs,Xl4_full,Yl4_full);
	v_prev := Vector([ Evaluate(f,Eltseq(Xl4_prev)) : f in RiemEQs ]);
	u_prev := Phi(CorrEQs,Xl4_prev,Yl4_prev);
	q := char^r;
	print "Full u:", m where m := Min([ Valuation(c) : c in Eltseq(u_full) ]);
	print "Full v:", m where m := Min([ Valuation(c) : c in Eltseq(v_full) ]);
	print "Prev u:", m where m := Min([ Valuation(c) : c in Eltseq(u_prev) ]);
	print "Prev v:", m where m := Min([ Valuation(c) : c in Eltseq(v_prev) ]);
	assert &and[ c eq 0 : c in Eltseq(u_full) ];
	print "Checking time #2:", Cputime(tyme);
    end if;
    return Xl4_full;
end function;    

intrinsic CanonicalLiftLevel4ThetaNullPoint(
    tt::SeqEnum[FldFinElt], prec:RngIntElt) -> SeqEnum
    {The 4-theta null point of the canonical lift is computed to precision prec.}
    FF := Universe(tt);
    char := Characteristic(FF);
    require char eq 3 : "Argument 1 must have universe a finite field of characteristic 3.";
    require #tt eq 10 : "Argument 1 must consist of ten theta constants.";
    require prec ge 1 : "Argument 2 must be a positive integer.";
    require IsValidLevel4ThetaNullPoint(tt) :
	"Argument 1 is not a valid level 4 theta null point.";
    
    if Degree(DefiningPolynomial(FF)) ne Degree(FF) then
	KK := FiniteField(#FF);	Embed(FF,KK);
	tt := ChangeUniverse(tt,KK);
	FF := KK;
    end if;
    RR := pAdicQuotientRing(char,prec);
    PZ := PolynomialRing(Integers());
    SS := UnramifiedExtension(RR,PZ!DefiningPolynomial(FF));
    AssignNames(~SS,["t"]);
    KK := ResidueClassField(SS); Embed(FF,KK);
    
    // Define modular equations
    P10 := PolynomialRing(Integers(),10);
    // xx := [ P10.i : i in [1..10] ];
    // RiemEQs_1 := Level4ThetaNullRiemannRelations(xx);
    RiemEQs := RiemannRelations(P10);
    DRiemEQs := Matrix([[ Derivative(f,i) : i in [2..10]] : f in RiemEQs ]);
    P20 := PolynomialRing(Integers(),20);
    x1 := [ P20.i : i in [ 1..10] ];
    x2 := [ P20.i : i in [11..20] ];
    CorrEQs_1 := Level4ThetaNullCorrespondenceRelations(x1,x2,char);
    CorrEQs := CorrespondenceRelations(P20,char);
    DCorrEQs := Matrix([[ Derivative(f,i) : i in ([2..10] cat [12..20])] : f in CorrEQs ]);
    // Preprocess so that the Riemann equations are satisfied to full precision...
    TT := ChangeUniverse(tt,SS);
    T2 := Level4ThetaNullPointToIsogenousLevel2ThetaNullPoint(TT);
    TT := Level4ThetaNullPointFromIsogenousLevel2ThetaNullPointHensel(T2,TT);
    // then lift...
    TT := NewtonThetaLift(TT,CorrEQs,DCorrEQs,RiemEQs,DRiemEQs);
    return TT;
end intrinsic;
