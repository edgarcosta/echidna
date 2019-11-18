//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Copyright (C) 2004 David Kohel <kohel@maths.usyd.edu.au>                //
//  Copyright (C) 2004 Christophe Ritzenthaler <ritzenth@math.jussieu.fr>   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

forward NewtonAGMLift;

/*

Currently "Level2ThetaCurveCoefficients" refers to [a1,a2,a3,e1,e2,e3] such that
y^2 + v(x)y = v(x)u(x) where v(x) = (x-e1)(x-e3)(x-e5) and u(x) is defined
such that a1 = u(e1)/v'(e1), a2 = u(e3)/v'(e3), and a2 = u(e5)/v'(e5).

These constants encode the data of Rosenhain invariants, in the sense that
a lift to characteristic zero is given by:

    Y^2 = (X-e1)(X-e2)(X-e3)(X-e4)(X-e5)(X-e6),

where e2 = e1 + 4a1,  e4 = e3 + 4a1, and e6 = e5 + 4a3.  On the other hand,
they determine a true level 2 theta null point (1 : 2x1 : 2x2 : 2x3), where

    x1 = sqrt(a1a3)/(e1-e5),
    x2 = sqrt(a1a2)/(e1-e3),
    x3 = sqrt(a2a3)/(e3-e5).

The need to extract square roots suggest that "Level2ThetaCurveCoefficients"
is a misnomer, the space of "AffineLevel2ThetaNullPoints" (x1,x2,x3) has a
degree 4 map (one square root is determined from (a1,a2,a3) from the other
two) to some invariants space of [a1,a2,a3,e1,e2,e3]. The latter space is
a special fiber of the space of Rosenhain invariants.

It would be desirable to make the "Level2ThetaCurveCoefficients" into invariants
by an appropriate normalization, say, [e1,e3,e5] -> [0,1,oo].  Doing so, one
obtains (transforming the curve y^2 + v(x)y = v(x)u(x) in the above form):

   a1 = u(0) = x2*x3/x1
   a2 = u(1) = x1*x2/x3
   a3 = u(oo) = (the leading coefficient) = x1*x3/x2

and that u(x) has an arbitrary linear factor x-x0 for x0 not in {0,1}.

N.B. Set u = (x-x0)(ax^2 + bx + c), then

   a1 = c*x0, hence c = x2*x3/(x1*x0),
   a3 = a = x1*x3/x2,

and a + b + c = a2/(1+x0) = x1*x3/(x2*(1+x0)) from which we can solve for b.

The resulting curve is of the form y^2 + x(x+1)y = (x+x0)(ax^2 + bx + c), and
its invariants are independent of x0.

REMARK: "Level2ThetaCurveCoefficients" represents a characteristic 2 analogue
of Rosenhain invariants; and the above gives a more canonical normalization 
such that [a1,a2,a3] = [x2*x3/x1,x1*x2/x3,x1*x3/x2].  The space of points [x1,x2,x3],
here called an "AffineLevel2ThetaNullPoint" is a special parametrization of
the neighborhood of (1:0:0:0) in (residue) characteristic 2.
*/

intrinsic HyperellipticCurveFromAffineLevel2ThetaNullPoint(
    xx::SeqEnum[RngElt] : BasePoint := 0) -> CrvHyp
    {Given an affine level 2 theta null pont [x1,x2,x3] returns the
    hyperelliptic curve y^2 + v(x)*y = v(x)u(x) where v(x) = x*(x+1)
    and u(x) = (x+x0)*(x1*x3/x2*x^2 +
    (x0*x1^2*x2 + x0*x2*x3^2 + x2*x3^2)/(x0^2*x1*x3 + x0*x1*x3)*x +
    (x0^2*x1^2*x3 + x0*x1^2*x3 + x2^2*x3)/(x0*x1*x2)) for an
    auxillary base point x0.}
    FF := Universe(xx);
    require Characteristic(FF) eq 2 :
	"Argument must be defined over a field of characteristic 2.";
    x1, x2, x3 := Explode(xx);
    PF := PolynomialRing(FF); x := PF.1;
    if BasePoint eq 0 then
	x0 := FF.1;
    else
	x0 := BasePoint;
    end if;
    v := x*(x+1);
    u := x1*x3/x2*x^3 + (x0^3*x1^2*x3^2 + x0*x1^2*x2^2 + x0*x1^2*x3^2 + x0*x2^2*x3^2
        + x2^2*x3^2)/(x0^2*x1*x2*x3 + x0*x1*x2*x3)*x^2 + (x0^3*x1^2*x3^2 + x0^2*x1^2*x2^2
        + x0^2*x1^2*x3^2 + x0^2*x2^2*x3^2 + x2^2*x3^2)/(x0^2*x1*x2*x3 + x0*x1*x2*x3)*x + x2*x3/x1;
    bool, C := IsHyperellipticCurve([u*v,v]);
    require bool : "Argument must define a nonsingular hyperelliptic curve.";
    return C;
end intrinsic;

intrinsic HyperellipticCurveFromLevel2ThetaCurveCoefficients(tt::SeqEnum[RngElt]) -> CrvHyp
    {Given tt = [a1,a2,a3,e1,e3,e5] return the hyperelliptic curve
    y^2 + v(x)*y = v(x)u(x) where v(x) = (x-e1)(x-e3)(x-e5) and
    where u(x) equals a1 (x-e3)(x-e5) + a2 (x-e1)(x-e5) + a3 (x-e1)(x-e3).
    N.B. The sequence determines a level 2 theta null point at 2 despite
    degeneracy at 2 (to (1:0:0:0)).}
    FF := Universe(tt);
    require Characteristic(FF) eq 2 :
	"Argument must be defined over a field of characteristic 2.";
    PF := PolynomialRing(FF); x := PF.1;
    a1, a2, a3, e1, e3, e5 := Explode(tt);
    u := a2*(x-e1)*(x-e5) + a3*(x-e1)*(x-e3) + a1*(x-e3)*(x-e5);
    v := (x-e1)*(x-e3)*(x-e5);
    bool, C := IsHyperellipticCurve([u*v,v]);
    require bool :
        "Argument must define a nonsingular hyperelliptic curve.";
    return C;
end intrinsic;

function pAdicFieldOfFractions(R)
    if Type(R) eq FldPad then
	return R;
    elif Type(R) eq RngPadRes then
	return pAdicField(Prime(R),Precision(R));
    elif Type(R) eq RngPadResExt then
	F := pAdicFieldOfFractions(BaseRing(R));
	return ext< F | DefiningPolynomial(R) >;
    end if;
    return FieldOfFractions(R);
end function;

function pAdicPreimageRing(R)
    S := pAdicRing(Prime(R),Precision(R));
    if Type(R) eq RngPadRes then
	return S;
    elif Type(R) eq RngPadResExt then
	return ext< S | DefiningPolynomial(R) >;
    end if;
end function;

intrinsic Level2ThetaCurveCoefficientsToRosenhainInvariants(cc::[RngElt]) -> SeqEnum
    {Given invariants [a1,a2,a3,e1,e3,e5] of the curve y^2 + v*y = v*u,
    where 

    v = (x-e1)*(x-e3)*(x-e5), and 
    u = a1*(x-e3)*(x-e5) + a2*(x-e1)*(x-e5) + a3*(x-e1)*(x-e3),

    returns the Rosenhain invariants [t0,t1,t2] of [e1,e2,e3,e4,e5,e6],
    such that ei are roots of (4*u + v)*v.}
    
    R := Universe(cc);
    require Type(R) in {RngPad,RngPadRes,RngPadResExt,FldPad} :
	"Argument must be defined over a 2-adic ring."; 
    require Prime(R) eq 2 : 
	"Argument must be defined over a 2-adic ring."; 
    a1,a2,a3,e1,e3,e5 := Explode(cc);
    x := PolynomialRing(R).1;
    /*
    FF<a1,a2,a3,e1,e3,e5> := FunctionField(ZZ,6);
    P<x> := PolynomialRing(FF); 
    v := (x-e1)*(x-e3)*(x-e5);
    u := a1*(x-e3)*(x-e5) + a2*(x-e1)*(x-e5) + a3*(x-e1)*(x-e3);
    g := 4*u + v; // factor of 4*u*v + v^2
    */
    g := x^3 + (4*(a1+a2+a3)-(e1+e3+e5))*x^2
        - (4*(a1*e3+a1*e5+a2*e1+a2*e5+a3*e1+a3*e3)-(e1*e3+e1*e5+e3*e5))*x
        + (4*(a1*e3*e5+a2*e1*e5+a3*e1*e3)-e1*e3*e5);
    e2 := HenselLift(g,e1-4*a1);
    e4 := HenselLift(g,e3-4*a2);
    e6 := HenselLift(g,e5-4*a3);
    K := pAdicFieldOfFractions(R);
    ee := [ K!Eltseq(ei) : ei in [e2,e4,e6,e1,e3,e5] ];
    return [ ((ee[i]-ee[4])*(ee[5]-ee[6])) div ((ee[i]-ee[6])*(ee[5]-ee[4])) : i in [1..3] ];
end intrinsic;

intrinsic Level2ThetaCurveCoefficientsOverSplittingField(C::CrvHyp[FldFin]) -> SeqEnum
    {Returns level 2 theta curve coefficients (a1,a2,a3,e1,e3,e5) such that
    the curve y^2 + v(x)y = v(x)u(x) is isomorphic to the input curve C,
    where v(x) = (x-e1)(x-e3)(x-e5) and u(x) equals a1 (x-e3)(x-e5) +
    a2 (x-e1)(x-e5) + a3 (x-e1)(x-e3).}
    FF := BaseRing(C);
    require Characteristic(FF) eq 2 : 
	"Argument must be over a field of characteristic 2 and degree at least 2.";
    f, v := HyperellipticPolynomials(C);
    if Degree(v) eq 2 then
	// Send the points over [0,1,oo] to points over [0,1,w]. 
	rts := { r[1] : r in Roots(v) };
	if #FF le #rts then
	    FF := FiniteField(2,2*Degree(FF));
	    C := BaseExtend(C,FF);
	end if;
	repeat
	    w := Random(FF);
	until w notin rts;
	C := Transformation(C,[1+w,0,1,w]); // u = 1+w as image of oo.
	f, v := HyperellipticPolynomials(C);
    end if;
    require f mod v eq 0 : 
	"Hyperelliptic polynomials must vanish on Weierstrass points.";
    require Degree(v) eq 3 and IsSquarefree(v) : 
	"Argument must be ordinary with affine Weierstrass points.";
    rts := [ r[1] : r in Roots(PolynomialRing(SplittingField(v))!v) ];
    FF := Universe(rts);
    e1, e3, e5 := Explode(rts);
    u := f div v;
    if Degree(u) eq 3 then
	if Coefficient(v,0) eq 0 then
	    ee := {e1,e3,e5};
	    repeat
		w := Random(FF);
	    until w notin ee;
	    C := Transformation(C,[1,w,0,1]);
	    e1 +:= w; e3 +:= w; e5 +:= w;
	    f, v := HyperellipticPolynomials(C); u := f div v;
	end if;
	u0 := Coefficient(u,0);
	if u0 ne 0 then
	    v0 := Coefficient(v,0);
	    g := Polynomial([u0*v0,v0,1]);
	    if IsIrreducible(g) then
		FF := FiniteField(2,2*Degree(FF));
		C := BaseExtend(C,FF);
		e1 := FF!e1; e3 := FF!e3; e5 := FF!e5;
		g := PolynomialRing(FF)!g;
		v := PolynomialRing(FF)!v;
	    end if;
	    w := Roots(g)[1][1];
	    C := Transformation(C,(v0^-1*w)*v);
	    f, v := HyperellipticPolynomials(C); u := f div v;
	    assert Coefficient(u,0) eq 0;
	end if;
	C := Transformation(C,[0,1,1,0]);
	e1 := e1^-1; e3 := e3^-1; e5 := e5^-1;
	f, v := HyperellipticPolynomials(C); u := f div v;
    end if;
    c := LeadingCoefficient(v);
    a1 := Evaluate(u,e1)/(c*(e1-e3)*(e1-e5));
    a2 := Evaluate(u,e3)/(c*(e3-e1)*(e3-e5));
    a3 := Evaluate(u,e5)/(c*(e5-e1)*(e5-e3));
    return [ a1, a2, a3, e1, e3, e5 ];
end intrinsic;

intrinsic Level2ThetaCurveCoefficientsFromIgusaInvariantsOverSplittingField(
    JJ::SeqEnum[FldFinElt]) -> SeqEnum
    {Returns level 2 theta curve coefficients [a1,a2,a3,e1,e3,e5] such that the
    curve y^2 + v(x)y = v(x)u(x) has given Igusa invariants JJ (with JJ[1] \ne 0,
    where v(x) = (x-e1)(x-e3)(x-e5) and u(x) equals a1 (x-e3)(x-e5) +
    a2 (x-e1)(x-e5) + a3 (x-e1)(x-e3).}
    FF := Universe(JJ);
    require JJ[1] ne 0 and #JJ eq 5 :
	"Argument must be a sequence ordinary Igusa invariants (of length 5).";
    require Characteristic(FF) eq 2 :
	"Argument must be defined over a field of characteristic 2.";
    C := HyperellipticCurveFromIgusaInvariants(JJ);
    return Level2ThetaCurveCoefficientsOverSplittingField(C);
end intrinsic;

intrinsic Level2ThetaNullPointFromAffineLevel2ThetaNullPoint(xx::[RngElt]) -> SeqEnum
    {Given an affine level 2 theta null point (x1,x2,x3) returns its image 
    under the projective embedding (x1,x2,x2) |-> (1:2*x1:2*x2:2*x3) 
    in the moduli space of level 2 theta null points.}
    require #xx eq 3 : "Argument must have length 3.";
    return [1] cat [ 2*xi : xi in xx ];
end intrinsic;

intrinsic AffineLevel2ThetaNullPointFromLevel2ThetaCurveCoefficients(tt::[RngElt]) -> SeqEnum
    {Given level 2 theta curve coefficients (a1,a2,a3,e1,e3,e5), returns
    the affine level 2 theta null point (x1,x2,x3) which gives a local
    parametrization of the level 2 theta null points, as (1:2*x1:2*x2:2*x3).}
    require #tt eq 6 : "Argument must have length 6.";
    a1, a2, a3, e1, e3, e5 := Explode(tt);
    bool, c1 := IsSquare(a1*a3);
    require bool : "Argument [a1,a2,a3,e1,e3,e5] must have square value a1*a3."; 
    bool, c2 := IsSquare(a1*a2);
    require bool : "Argument [a1,a2,a3,e1,e3,e5] must have square value a1*a2."; 
    c3 := c1*c2/a1;
    return [ c1/(e1-e5), c2/(e1-e3), c3/(e3-e5) ]; 
end intrinsic;

intrinsic AffineLevel2ThetaNullPointToLevel2ThetaCurveCoefficients(
    xx::[RngElt] : BasePoint := 0) -> SeqEnum
    {Given an affine level 2 theta null point (x1,x2,x3) which gives a local
    parametrization of the level 2 theta null points, as (1:2*x1:2*x2:2*x3),
    returns the associated level 2 theta curve coefficients (a1,a2,a3,e1,e3,e5)
    for y^2 + v(x)y = v(x)u(x) where v(x) = (x-e1)(x-e3)(x-e5) and u(x) equals
    a1 (x-e3)(x-e5) + a2 (x-e1)(x-e5) + a3 (x-e1)(x-e3).}
    FF := Universe(xx);
    require #xx eq 3 : "Argument must have length 3.";
    x0 := BasePoint ne 0 select FF!BasePoint else FF.1; 
    require x0 ne 0 and x0 ne 1 :
	"Parameter BasePoint must be specified, different from 0 or 1.";
    x1, x2, x3 := Explode(xx);
    a1 := x0*x1*x2/(x3*(1-x0));
    a2 := (1-x0)*x2*x3/(x0*x1);
    a3 := (1-x0)*x0*x1*x3/x2;
    return [a1,a2,a3,0,1,x0];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// AGM lifting algorihtm for 2-theta null points (characteristic 2)
//////////////////////////////////////////////////////////////////////////////

function Phi2(xx,yy)
    x1, x2, x3 := Explode(xx);
    y1, y2, y3 := Explode(yy);
    sym_y := 1 + 4*(y1^2 + y2^2 + y3^2);
    return [ y1 - x1^2*sym_y + 2*y2*y3,	y2 - x2^2*sym_y + 2*y1*y3, y3 - x3^2*sym_y + 2*y1*y2 ];
end function;

function DxPhi2(xx,yy)
    x1, x2, x3 := Explode(xx);
    y1, y2, y3 := Explode(yy);
    sym_y := 1 + 4*(y1^2 + y2^2 + y3^2);
    return DiagonalMatrix([ -2*x1*sym_y, -2*x2*sym_y, -2*x3*sym_y ]);
end function;

function DyPhi2(xx,yy)
    x1, x2, x3 := Explode(xx);
    y1, y2, y3 := Explode(yy);
    return Matrix([
	[ 1 - 8*x1^2*y1,     2*y3 - 8*x2^2*y1, 2*y2 - 8*x3^2*y1 ],
	[ 2*y3 - 8*x1^2*y2,  1 - 8*x2^2*y2,    2*y1 - 8*x3^2*y2	],
	[ 2*y2 - 8*x1^2*y3,  2*y1 - 8*x2^2*y3, 1 - 8*x3^2*y3	] ]);
end function;

function Phi3(xx,yy)
    x1, x2, x3 := Explode(xx);
    y1, y2, y3 := Explode(yy);
    return [
	(x1+y1)^8 + x1*y1*(x1+y1)^4 + (y1*x2*x3 + x1*y2*y3)^2,
	(x2+y2)^8 + x2*y2*(x2+y2)^4 + (x1*y2*x3 + y1*x2*y3)^2,
	(x3+y3)^8 + x3*y3*(x3+y3)^4 + (x1*x2*y3 + y1*y2*x3)^2,
	x1^4 + x2^4 + y1^4 + y2^4 + x1*y1 + x2*y2,
	x1^4 + x3^4 + y1^4 + y3^4 + x1*y1 + x3*y3,
	x2^4 + x3^4 + y2^4 + y3^4 + x2*y2 + x3*y3 
	];
end function;

/*
> F<x1,x2,x3,y1,y2,y3> := PolynomialRing(GF(2),6);
> xx := [x1,x2,x3];
> yy := [y1,y2,y3];
> AffineLevel2ThetaNullCorrespondenceRelations(xx,yy,2);
[
    x1^2 + y1,
    x2^2 + y2,
    x3^2 + y3
]
> AffineLevel2ThetaNullCorrespondenceRelations(xx,yy,3);
[
    x1^8 + x1^5*y1 + x1^2*y2^2*y3^2 + x1*y1^5 + x2^2*x3^2*y1^2 + y1^8,
    x1^2*x3^2*y2^2 + x2^8 + x2^5*y2 + x2^2*y1^2*y3^2 + x2*y2^5 + y2^8,
    x1^2*x2^2*y3^2 + x3^8 + x3^5*y3 + x3^2*y1^2*y2^2 + x3*y3^5 + y3^8,
    x1^4 + x1*y1 + x2^4 + x2*y2 + y1^4 + y2^4,
    x1^4 + x1*y1 + x3^4 + x3*y3 + y1^4 + y3^4,
    x2^4 + x2*y2 + x3^4 + x3*y3 + y2^4 + y3^4
]
*/

intrinsic AffineLevel2ThetaNullCorrespondenceRelations(
    xx::SeqEnum[RngElt],yy::SeqEnum[RngElt],p::RngIntElt) -> SeqEnum
    {Given xx = (x1,x2,x3) and yy = (y1,y2,y3), returns the correspondence
    relations determined by (p,p)-isogenies (for p = 2 or 3) in terms of the affine
    images tt = (1:1+2*x1:1+2*x2:1+2*x3) and uu = (1:1+2*y1:1+2*y2:1+2*y3).}
    case p:
    when 2:
	return Phi2(xx,yy);
    when 3:
	R := Universe(xx);
	require Characteristic(R) eq 2 :
	    "Arguments 1 and 2 must be defined over a ring of characteristic 2.";
	return Phi3(xx,yy);
    else
	require false : "Argument 3 must be 2 or 3.";
    end case;
end intrinsic;

intrinsic CanonicalLiftAffineLevel2ThetaNullPoint(xx::[FldFinElt],prec::RngIntElt) -> SeqEnum
    {The canonical lift of the given 2-theta null point in characteristic 2
    is computed to precision prec.  The 2-theta null point tt is represented
    by the point xx = (x1,x2,x3) such that tt = (1:1+2*x1:1+2*x2:1+2*x3) is
    the theta null point modulo 4.}

    require #xx eq 3  and Characteristic(Universe(xx)) eq 2 :
        "Argument must consist of 3 elements over of field of characteristic 2.";
    n := Degree(Universe(xx));
    Z2 := pAdicQuotientRing(2,prec);
    SS := UnramifiedExtension(Z2,n);
    return NewtonAGMLift(ChangeUniverse(xx,SS));
end intrinsic;

function NewtonAGMLift(xx)
    SS := Universe(xx);
    prec := Precision(SS);
    if prec eq 1 then return xx; end if;
    p := ResidueCharacteristic(SS);
    prec1 := (prec+1) div 2;
    
    vprintf CanonicalLift : "REDUCING TO LOWER PRECISION: %o\n", prec1;

    S1 := ChangePrecision(SS,prec1); AssignNames(~S1,["t"]);
    xx_half_S1 := NewtonAGMLift(ChangeUniverse(xx,S1));
    yy_half_S1 := [ FrobeniusImage(xi) : xi in xx_half_S1 ];

    vprintf CanonicalLift : "LIFTED HALFWAY TO PRECISION: %o\n", prec1;
    
    xx_half_SS := ChangeUniverse(xx_half_S1,SS);
    yy_half_SS := [ FrobeniusImage(xi) : xi in xx_half_SS ];
    DY := DyPhi2(xx_half_S1,yy_half_S1); // == I mod p
    DX := DxPhi2(xx_half_S1,yy_half_S1); // == 0 mod p
    cc := Vector([ S1 | uu div p^prec1 : uu in Phi2(xx_half_SS,yy_half_SS) ]);

    tyme := Cputime();
    delta := ArtinSchreierRoot(DY,DX,cc);
    vprint CanonicalLift, 2 : "  Artin-Schreier root time:", Cputime(tyme);
    delta_sig := Vector([ FrobeniusImage(delta[i]) : i in [1..3] ]);
    return [ xx_half_SS[i] + p^prec1*(SS!delta[i]) : i in [1..3] ]; 
end function;

//////////////////////////////////////////////////////////////////////////////
// Canonical lifting algorithm using naive AGM iteration
//////////////////////////////////////////////////////////////////////////////

chars := [ VectorSpace(FiniteField(2),2) | [0,0], [1,0], [0,1], [1,1] ];

function pAdicRingLift(S)
    P := PolynomialRing(Rationals());
    R := pAdicRing(Prime(S),Precision(S));
    return UnramifiedExtension(R,P!DefiningPolynomial(S));
end function;

function DuplicationFormula(B,vv)
    v1, v0 := Explode(vv);
    a := 0;
    for j in [1..4] do
	vj := chars[j]; uj := vj + v0;
	sj := IntegerRing()!InnerProduct(vj,v1);
	Aj := B[Index(chars,vj)];
	Bj := B[Index(chars,uj)];
        a +:= (-1)^sj * Aj * Sqrt(Bj div Aj);
    end for;
    return a div 4;
end function;

function Duplicate0(B)
    return [ DuplicationFormula(B,[chars[i],chars[1]]) : i in [1..4] ];
end function;

function Duplicate1(B)
    return [ DuplicationFormula(B,[chars[1],chars[j]]) : j in [1..4] ];
end function;

/*
[
    DuplicationFormula(B,[[0,0],[0,0]]),
    DuplicationFormula(B,[[0,0],[1,0]]),
    DuplicationFormula(B,[[0,0],[0,1]]),
    DuplicationFormula(B,[[0,0],[1,1]])
];
*/

intrinsic CanonicalLiftLevel2ThetaCurveCoefficients(C::[FldFinElt],prec::RngIntElt : 
    Iterations := 0) -> SeqEnum
    {Canonical lift using naive AGM iteration of duplication formula
    for level 2 theta curve coefficients [a1,a2,a3,e1,e3,e5].}
    F := Universe(C);
    require Characteristic(F) eq 2 :
        "Universe of argument must be finite field of characteristic 2.";
    require #C eq 6 : "Argument must be a sequence of 6 elements.";

    if Iterations eq 0 then Iterations := prec div 4; end if;
    
    n := Degree(F);
    R := pAdicQuotientRing(2,prec);
    S := CyclotomicUnramifiedExtension(R,n);
    K, phi := ResidueClassField(S);
    assert DefiningPolynomial(K) eq DefiningPolynomial(F);
    
    a1_0, a2_0, a3_0, e1_0, e3_0, e5_0 := Explode(C);
    P := PolynomialRing(F); X := P.1;
    U := a2_0*(X-e1_0)*(X-e5_0) +
        a3_0*(X-e1_0)*(X-e3_0) + a1_0*(X-e3_0)*(X-e5_0);
    V := (X-e1_0)*(X-e3_0)*(X-e5_0);
    require IsHyperellipticCurve([U*V,V]) :
        "Argument must define a nonsingular genus 2 curve.";

    a1 := S!(K!Eltseq(a1_0));
    a2 := S!(K!Eltseq(a2_0));
    a3 := S!(K!Eltseq(a3_0));
    e1 := S!(K!Eltseq(e1_0));
    e3 := S!(K!Eltseq(e3_0));
    e5 := S!(K!Eltseq(e5_0));
    e2 := e1 + 4*a1; e4 := e3 + 4*a2; e6 := e5 + 4*a3;
    
    P := PolynomialRing(F); X := P.1;
    
    Asq := (e1-e3)*(e3-e5)*(e5-e1)*(e2-e4)*(e4-e6)*(e6-e2);
    Bsq := (e1-e3)*(e3-e6)*(e6-e1)*(e2-e4)*(e4-e5)*(e5-e2);
    Csq := (e1-e4)*(e4-e5)*(e5-e1)*(e2-e3)*(e3-e6)*(e6-e2);
    Dsq := (e1-e4)*(e4-e6)*(e6-e1)*(e2-e3)*(e3-e5)*(e5-e2);
    
    ABCD := [1,Sqrt(Bsq div Asq),Sqrt(Csq div Asq),Sqrt(Dsq div Asq)];

    vprint CanonicalLift : "Target precision:", Precision(S);

    tyme := Cputime();
    for i in [1..Iterations+n] do
	if i mod 32 eq 1 then
	    Si := ChangePrecision(S,Min(64*(i+1),prec));
	    ABCD := ChangeUniverse(ABCD,Si);
	end if;
	ABCD := Duplicate1(ABCD);
    end for;
    vprint CanonicalLift : "Theta null invariant lifting:", Cputime(tyme);

    tyme := Cputime();
    t00 := DuplicationFormula(ABCD,[chars[1],chars[1]]); // [[0,0],[0,0]]
    t01 := DuplicationFormula(ABCD,[chars[2],chars[1]]); // [[1,0],[0,0]]
    t02 := DuplicationFormula(ABCD,[chars[3],chars[1]]); // [[0,1],[0,0]]
    t03 := DuplicationFormula(ABCD,[chars[4],chars[1]]); // [[1,1],[0,0]]
    t04 := DuplicationFormula(ABCD,[chars[1],chars[2]]); // [[0,0],[1,0]]
    t06 := DuplicationFormula(ABCD,[chars[3],chars[2]]); // [[0,1],[1,0]]
    t08 := DuplicationFormula(ABCD,[chars[1],chars[3]]); // [[0,0],[0,1]]
    t09 := DuplicationFormula(ABCD,[chars[2],chars[3]]); // [[1,0],[0,1]]
    t12 := DuplicationFormula(ABCD,[chars[1],chars[4]]); // [[0,0],[1,1]]
    t15 := DuplicationFormula(ABCD,[chars[4],chars[4]]); // [[1,1],[1,1]]
    vprint CanonicalLift : "Theta invariant time:", Cputime(tyme);

    return [t00,t01,t02,t03,t04,t06,t08,t09,t12,t15];
end intrinsic;

intrinsic CanonicalLiftIgusaInvariantRelations(C::[FldFinElt],prec::RngIntElt : 
    Iterations := 0,  RelationDegree := 0, RelationPrecision := 0, Invariants := "Igusa")
    -> SeqEnum, SeqEnum, SeqEnum
    {Canonical lift of Igusa invariants using naive AGM iteration of duplication
    formula for level 2 theta null curve coefficients.}
    F := Universe(C);
    require Characteristic(F) eq 2 :
        "Universe of argument must be finite field of characteristic 2.";

    require #C eq 6 : "Argument must be a sequence of 6 elements.";

    a1_0, a2_0, a3_0, e1_0, e3_0, e5_0 := Explode(C);
    P := PolynomialRing(F); X := P.1;
    U := a2_0*(X-e1_0)*(X-e5_0) +
        a3_0*(X-e1_0)*(X-e3_0) + a1_0*(X-e3_0)*(X-e5_0);
    V := (X-e1_0)*(X-e3_0)*(X-e5_0);
    require IsHyperellipticCurve([U*V,V]) :
        "Argument must define a nonsingular genus 2 curve.";

    if Iterations eq 0 then Iterations := prec; end if;
    
    deg := RelationDegree;

    tt := CanonicalLiftLevel2ThetaCurveCoefficients(C,prec : Iterations := Iterations);
    t00,t01,t02,t03,t04,t06,t08,t09,t12,t15 := Explode(tt);

    S := Universe(tt);
    Q := pAdicRingLift(S); // Field of fractions

    l1 := -Q!Eltseq(t04*t06)/Q!Eltseq(t03*t01);
    l2 := -Q!Eltseq(t12*t06)/Q!Eltseq(t03*t09);
    l3 := -Q!Eltseq(t12*t04)/Q!Eltseq(t01*t09);

    PP<X> := PolynomialRing(Parent(l1));
    ff := X*(X-1)*(X-l1)*(X-l2)*(X-l3);

    if Invariants eq "IgusaClebsch" then
	II := IgusaClebschInvariants(ff);
	i1 := II[1]^5/II[4];        // I_2^5/I_10
	i2 := II[1]^3*II[2]/II[4];  // I_4 I_2^3/I_10
	i3 := II[1]^2*II[3]/II[4];  // I_6 I_2^2/I_10
	n1 := Valuation(i1); i1_0 := S!Eltseq(2^-n1*i1);
	n2 := Valuation(i2); i2_0 := S!Eltseq(2^-n2*i2);
	n3 := Valuation(i3); i3_0 := S!Eltseq(2^-n3*i3);
    elif Invariants eq "Clebsch" then
	II := ClebschInvariants(ff);
	A, B, C, D := Explode(II);
	U := (-62208*A^5 + 972000*A^3*B + 1620000*A^2*C
	    - 3037500*A*B^2 - 6075000*B*C - 4556250*D)^-1;
	i1 := A^5*U;    // A^5/Delta
	i2 := A^3*B*U;  // A^2*B/Delta
	i3 := A^2*C*U;  // A*C/Delta
	n1 := Valuation(i1); i1_0 := S!Eltseq(2^-n1*i1);
	n2 := Valuation(i2); i2_0 := S!Eltseq(2^-n2*i2);
	n3 := Valuation(i3); i3_0 := S!Eltseq(2^-n3*i3);
    elif Invariants eq "Igusa" then
	JJ := IgusaInvariants(ff);
	i1 := JJ[1]^5/JJ[5];        // J_2^5/J_10
	i2 := JJ[1]^3*JJ[2]/JJ[5];  // J_2^3 J_4/J_10
	i3 := JJ[1]*JJ[4]/JJ[5];  // J_2 J_8/J_10
	n1 := Valuation(i1); 
	i1_0 := S!Eltseq(2^-n1*i1);
	n2 := Valuation(i2); 
	i2_0 := S!Eltseq(2^-n2*i2);
	n3 := Valuation(i3); 
	i3_0 := S!Eltseq(2^-n3*i3);
	assert n1 eq 0;
    else
	require false : "Invalid parameter \"Invariants\".";
    end if;

    vprint CanonicalLift : "Ring precision =", prec;
    rel_precs := [ RelativePrecision(ii) : ii in [i1,i2,i3] ];
    prec := Min(rel_precs);
    if false and Invariants ne "IgusaClebsch" then
	prec -:= 128;
    end if;
    if RelationPrecision ne 0 then
	prec := Min(RelationPrecision,prec);
    end if;
    vprint CanonicalLift : "Resetting precision to", prec;
    
    if deg gt 0 then
	S1 := ChangePrecision(S,prec);
	i1_0 := S1!i1_0; i2_0 := S1!i2_0; i3_0 := S1!i3_0;
	rel1 := AlgebraicRelations([i1_0],deg)[1];
	vprintf CanonicalLift : "%3o: %o\n", n1, rel1;
	rel2 := AlgebraicRelations([i2_0],deg)[1];
	vprintf CanonicalLift : "%3o: %o\n", n2, rel2;
	rel3 := AlgebraicRelations([i3_0],deg)[1];
	vprintf CanonicalLift : "%3o: %o\n", n3, rel3;
	rels := [ rel1, rel2, rel3 ];
    else
	rels := [];
    end if;
    igus := [ i1_0, i2_0, i3_0 ];
    vals := [ n1, n2, n3 ];
    return igus, rels, vals;
end intrinsic;





