//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   SINGULAR HYPERELLIPTIC CURVES                          //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

forward CantorReduction1, CantorReduction2;

////////////////////////////////////////////////////////////////////////
//                      Attribute declarations                        //
////////////////////////////////////////////////////////////////////////

declare attributes Crv:
    HyperellipticPolynomials;

declare type PicHypSng[PicHypSngElt];

declare attributes PicHypSng:
    Curve,
    Ring;

declare attributes PicHypSngElt:
    Parent,
    Divisor;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                 Singular Hyperelliptic Creation                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic SingularHyperellipticCurve(f::RngUPolElt,h::RngUPolElt) -> Crv
    {}
    require Parent(f) eq Parent(h) :
	"Arguments must have the same parents.";
    g := (Degree(f)-1) div 2;
    K := BaseRing(Parent(f));
    RXYZ := PolynomialRing(Rationals(),[1,g+1,1],"elim",2);
    P2<X,Y,Z> := ProjectiveSpace(RXYZ);
    fXZ := Homogenization(Evaluate(f,X),Z,2*g+2);
    hXZ := Homogenization(Evaluate(h,X),Z,g+1);
    C := Curve(P2,Y^2 + hXZ*Y - fXZ);
    fac := Factorization(4*f-h^2);
    //require &and[ ff[2] le 2 : ff in fac ] :
    //	"Argument's divisors must have multiplicity at most 2.";
    r := &*[ Parent(f) | ff[1]^(ff[2] div 2) : ff in fac | ff[2] gt 1 ];
    C`HyperellipticPolynomials := [f,h,r];
    return C;
end intrinsic;

intrinsic SingularHyperellipticCurve(f::RngUPolElt) -> Crv
    {}
    g := (Degree(f)-1) div 2;
    K := BaseRing(Parent(f));
    RXYZ := PolynomialRing(K,[1,g+1,1],"elim",2);
    P2<X,Y,Z> := ProjectiveSpace(RXYZ);
    fXZ := Homogenization(Evaluate(f,X),Z,2*g+2);
    C := Curve(P2,Y^2 - fXZ);
    fac := Factorization(f);
    //require &and[ ff[2] le 2 : ff in fac ] :
    //"Argument's divisors must have multiplicity at most 2.";
    r := &*[ Parent(f) | ff[1]^(ff[2] div 2) : ff in fac | ff[2] gt 1 ];
    C`HyperellipticPolynomials := [f,0,r];
    return C;
end intrinsic;

intrinsic HyperellipticPolynomials(C::Crv) -> RngUPolElt, RngUPolElt
    {}
    require assigned C`HyperellipticPolynomials :
	"Argument must have been created as a singular hyperelliptic.";
    return f, h, r where f, h, r := Explode(C`HyperellipticPolynomials);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Picard Group Creation                       //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic SingularPicardGroup(C::Crv) -> PicHypSng
    {The picard group of the singular hyperelliptic curve C.}
    require assigned C`HyperellipticPolynomials :
	"Argument must have been created as a singular hyperelliptic.";
    J := New(PicHypSng);
    J`Curve := C;
    return J;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Coercions                                  //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function HyperellipticDivisor(P)
    C := Scheme(P);
    x0, y0, z0 := Explode(Eltseq(P));
    x := Universe(C`HyperellipticPolynomials).1;
    if z0 eq 0 then return [Parent(x)|1,0]; end if;
    if z0 ne 1 then
	bool, u0 := IsInvertible(z0);
	assert bool;
	n, m, o := Explode(Gradings(Ambient(C))[1]);
	assert n eq 1 and o eq 1;
	x0 *:= u0; y0 *:= u0^m;
    end if;
    return [x-x0, y0];
end function;

intrinsic IsCoercible(J::PicHypSng,D::.)
    -> BoolElt, PicHypSngElt
    {The point on C defined by P.}
    if Type(D) eq PicHypSngElt and Parent(D) eq J then
	return true, D;
    elif Type(D) eq RngIntElt then
	if D ne 0 then
	    return false, "Invalid coercion.";
	end if;
	R := PolynomialRing(BaseRing(J`Curve));
	P := New(PicHypSngElt);
	P`Parent := J;
	P`Divisor := [R|1,0];
	return true, P;
    elif Type(D) eq Pt then
	if Scheme(D) ne J`Curve then
	    bool, D := IsCoercible(J`Curve,D);
	    if not bool then
		return false, "Invalid coercion.";
	    end if;
	end if;
	P := New(PicHypSngElt);
	P`Parent := J;
	P`Divisor := HyperellipticDivisor(D);
	return true, P;
    elif Type(D) eq SeqEnum then
	R := PolynomialRing(BaseRing(J`Curve));
	bool, D := CanChangeUniverse(D,R);
	if bool and #D eq 2 then
	    f, h, r := HyperellipticPolynomials(J`Curve);
	    require (D[2]^2+D[2]*h-f) mod D[1] eq 0 :
		"Invalid divisor coercion.";
	    if Degree(D[2]) ge Degree(D[1]) then
		D[2] mod:= D[1];
	    end if;
	    lc := LeadingCoefficient(D[1]);
	    if lc ne 1 then
		D[1] /:= lc;
	    end if;
	    if Degree(D[1]) gt (Degree(f)-1) div 2 then
		D := h eq 0 select
		    CantorReduction1(D[1],D[2],f) else
		    CantorReduction2(D[1],D[2],f,h);
	    end if;
	    P := New(PicHypSngElt);
	    P`Parent := J;
	    P`Divisor := D;
	    return true, P;
	end if;
    end if;
    return false, "Invalid coercion.";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Printing                                   //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(J::PicHypSng, level::MonStgElt)
    {}
    printf "Generalized Picard group of %o", J`Curve;
end intrinsic;

intrinsic Print(P::PicHypSngElt, level::MonStgElt)
    {}
    D := P`Divisor;
    if D[1] eq 1 then
	printf "(1)";
    elif D[2] eq 0 then
	printf "(%o, y)", D[1];
    else
	printf "(%o, y + %o)", D[1], -D[2];
    end if;
    return;
    // Using projective coordinates, the printing is more
    // difficult to read.
    C := Parent(P)`Curve;
    f, h := Explode(C`HyperellipticPolynomials);
    g := (Degree(f)-1) div 2;
    X := Ambient(C).1; Z := Ambient(C).3;
    AZ := Homogenization(Evaluate(D[1],X),Z,g);
    BZ := Homogenization(Evaluate(D[2],X),Z,g+1);
    if BZ eq 0 then
	printf "(%o, Y)", AZ;
    else
	printf "(%o, Y+%o)", AZ, -BZ;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            Parents                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Parent(P::PicHypSngElt) -> PicHypSng
    {The parent of P.}
    return P`Parent;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Membership and equality                        //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(P::PicHypSngElt,J::PicHypSng)
    -> BoolElt
    {Returns true if P is point on J.}
    return Parent(P) eq J;
end intrinsic;

intrinsic 'eq'(P::PicHypSngElt,Q::PicHypSngElt) -> BoolElt
    {}
    if Parent(P) ne Parent(Q) then return false; end if;
    return P`Divisor eq Q`Divisor;
end intrinsic; 

intrinsic 'eq'(J1::PicHypSng,J2::PicHypSng) -> BoolElt
    {}
    return Curve(J1) eq Curve(J2);
end intrinsic; 

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   Compact Represenation of Divisors                // 
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic CompactRepresentation(p::PicHypSngElt) -> RngUPolElt
    {}
    C := Curve(Parent(p));
    f, g, s := HyperellipticPolynomials(C);
    require g eq 0 : "Curve of argument must have the for y^2 = f.";
    r := f div s^2;
    D := p`Divisor;
    P := Universe(D); z := P.1;
    if Degree(r) eq 0 then
	print "Caution: compact representation is degenerate.";
	return D[1];
    elif Degree(r) eq 1 then
	xz := Coefficient(r,1)^-1*(z^2-Coefficient(r,0));
	yz := z*Evaluate(s,xz);	
    else
	require Degree(r) le 1 :
	    "Curve of argument must have geometric genus 0.";
    end if;
    return GCD(Evaluate(D[1],xz), yz-Evaluate(D[2],xz));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    CANTOR COMPOSITION AND REDUCTION                //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function DivisorInverse(C,D) //(C::Crv,D::[RngUPolElt]) -> SeqEnum
    //{}
    //require assigned C`HyperellipticPolynomials :
    //"Argument must have been created as a singular hyperelliptic.";
    f, h := Explode(C`HyperellipticPolynomials);
    return h eq 0 select [D[1],-D[2]] else [D[1],-h-D[2]];
end function;

intrinsic CantorExponentiation(
    C::Crv,D::[RngUPolElt],n::RngIntElt) -> SeqEnum
    {}
    if n lt 0 then
	return CantorExponentiation(C,DivisorInverse(C,D),-n);
    elif n eq 0 then
	return [Universe(D)|1,0];
    elif n eq 1 then
	return D;
    elif n eq 2 then
	return CantorComposition1(C,D,D);
    end if;
    bi := IntegerToSequence(n,2);
    Di := [Universe(D)|1,0];
    for i in [1..#bi] do
	if bi[i] ne 0 then
	    Di := CantorComposition1(C,Di,D);
	end if;
	D := CantorComposition1(C,D,D);
    end for;
    return Di;
end intrinsic;


intrinsic CantorComposition1(
    C::Crv,D1::[RngUPolElt], D2::[RngUPolElt]) -> SeqEnum
    {Composition of divisors}
    f, h, r := HyperellipticPolynomials(C);
    require h eq 0 :
	"Argument must be a simplified Weierstrass model.";
    a1, b1 := Explode(D1); 
    a2, b2 := Explode(D2); 
    if a1 eq a2 and b1 eq b2 then
	// Duplication law:
	d, h1, h3 := XGCD(a1, 2*b1);
	a := (a1 div d)^2;
	b := (b1 + h3*((f - b1^2) div d)) mod a;
    else
	d0, _, h2 := XGCD(a1, a2);
	if d0 eq 1 then
	    a := a1*a2; b := (b2 + h2*a2*(b1-b2)) mod a;
	else
	    d, l, h3 := XGCD(d0, b1 + b2);
	    a := (a1*a2) div d^2;
	    b := (b2 + l*h2*(b1-b2)*(a2 div d) + h3*((f - b2^2) div d)) mod a;
	end if;
    end if;
    g := (Degree(f)-1) div 2;
    if Degree(a) le g then return [a,b]; end if;
    return CantorReduction1(a,b,f);
end intrinsic;


intrinsic CantorComposition2(
    C::Crv,D1::[RngUPolElt], D2::[RngUPolElt]) -> SeqEnum
    {Composition of divisors.}
    f, h, r := HyperellipticPolynomials(C);
    a1, b1 := Explode(D1); 
    a2, b2 := Explode(D2); 
    if a1 eq a2 and b1 eq b2 then
	// Duplication law:
	d, h1, h3 := XGCD(a1, 2*b1 + h);
	a := (a1 div d)^2;
	b := (b1 + h3*((f-h*b1-b1^2) div d)) mod a;
    else
	d0, _, h2 := XGCD(a1, a2);
	if d0 eq 1 then
	    a := a1*a2;
	    b := (b2 + h2*a2*(b1-b2)) mod a;
	else
	    d, l, h3 := XGCD(d0, b1+b2+h);
	    a := (a1*a2) div d^2;
	    b := (b2 + l*h2*(b1-b2)*(a2 div d) + h3*((f-h*b2-b2^2) div d)) mod a;
	end if;
    end if;
    g := (Degree(f)-1) div 2;
    assert GCD(a,r) eq 1;
    if Degree(a) le g then return [a,b]; end if;
    return CantorReduction2(a,b,f,h);
end intrinsic;

function CantorReduction1(a1,b1,f)
    /*
    (a::RngUPolElt, b::RngUPolElt, f::RngUPolElt) -> RngUPolElt, RngUPolElt
    {Divisor reduction.}
    */
    g := (Degree(f)-1) div 2;
    a2 := (f - b1^2) div a1;
    a2 *:= 1/LeadingCoefficient(a2);
    b2 := -b1 mod a2;
    if Degree(a2) eq Degree(a1) then
	assert Degree(a2) eq g+1;
	print "Returning ambiguous form of degree g+1.";
	return [a2, b2];
    elif Degree(a2) gt g then
	return CantorReduction1(a2,b2,f);
    end if;
    return [a2, b2];
end function;

function CantorReduction2(a,b,f,h)
    /*
    (a::RngUPolElt, b::RngUPolElt, h::RngUPolElt, f::RngUPolElt)
    -> RngUPolElt, RngUPolElt
    {Divisor reduction.}
    */
    g := (Degree(f)-1) div 2;
    assert Degree(a) le 2*g;
    assert Degree(b) lt Degree(a);
    k := f - h*b - b^2;
    if 2*Degree(a) eq Degree(k) then
	// must adjust b to include the point at infinity
	g1 := Degree(a);
	x := Parent(a).1;
	r := Roots(x^2 + Coefficient(h,g1)*x - Coefficient(f,2*g1))[1][1];
	b := b + r*(x^g1 - (x^g1 mod a));
	k := f - h*b - b^2;
    end if;
    assert k mod a eq 0;
    a := k div a;
    a *:= 1/LeadingCoefficient(a);
    b := -(b+h) mod a;
    if Degree(a) gt g then
	return CantorReduction2(a,b,f,h);
    end if;
    assert Degree(a) le g;
    return [a, b];
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            Access                                  //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic BaseRing(J::PicHypSng) -> Rng
    {The base ring of J.}
    return BaseRing(J`Curve);
end intrinsic;

intrinsic Curve(J::PicHypSng) -> Crv
    {The defining curve of J.}
    return J`Curve;
end intrinsic;

intrinsic Dimension(J::PicHypSng) -> RngIntElt
    {The dimension of J.}
    return (Degree(HyperellipticPolynomials(J`Curve))-1) div 2;
end intrinsic;

intrinsic Eltseq(P::PicHypSngElt) -> SeqEnum
    {}
    return P`Divisor;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Arithmetic                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Identity(J::PicHypSng) -> PicHypSngElt
    {The identity element of J.}
    return J!0;
end intrinsic;

intrinsic '-'(P::PicHypSngElt) -> PicHypSngElt
    {}
    J := P`Parent;
    D := P`Divisor;
    f, h := Explode(J`Curve`HyperellipticPolynomials);
    return J!(h eq 0 select [D[1],-D[2]] else [D[1],-h-D[2]]);
end intrinsic;

intrinsic '-'(P::PicHypSngElt,Q::PicHypSngElt) -> PicHypSngElt
    {}
    return P+(-Q);
end intrinsic;

intrinsic '+'(P::PicHypSngElt,Q::PicHypSngElt) -> PicHypSngElt
    {}
    J := Parent(P);
    require J eq Parent(Q) : "Arguments must have the same parent.";
    return J!CantorComposition1(J`Curve,P`Divisor,Q`Divisor);
end intrinsic;

intrinsic '+:='(~P::PicHypSngElt,Q::PicHypSngElt)
    {}
    J := Parent(P);
    require J eq Parent(Q) : "Arguments must be in the same point set.";
    P`Divisor := CantorComposition1(J`Curve,P`Divisor,Q`Divisor);
end intrinsic;

intrinsic '*'(n::RngIntElt,P::PicHypSngElt) -> PicHypSngElt
    {}
    Q := New(PicHypSngElt);
    Q`Parent := P`Parent;
    Q`Divisor := CantorExponentiation((P`Parent)`Curve,P`Divisor,n);
    return Q;
end intrinsic;

intrinsic '*:='(~P::PicHypSngElt,n::RngIntElt)
    {}
    P`Divisor := CantorExponentiation((P`Parent)`Curve,P`Divisor,n);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             Random                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic PointsOfDegree(J::PicHypSng,d::RngIntElt) -> SeqEnum
    {The sequence of rational points of J represented by degree
    d divisors, up to hyperelliptic equivalence.}
    Pnts := [ J | ];
    K := BaseRing(J);
    C := Curve(J);
    P := PolynomialRing(K); x := P.1;
    if d gt 1 then
	f, h := HyperellipticPolynomials(C);
	Xcoords := { P | };
	for cff in CartesianPower(K,d) do
	    bx := &+[ cff[i]*x^(i-1) : i in [1..d] ];
	    for ff in Factorization(bx^2+bx*h-f) do
		if Degree(ff[1]) eq d and ff[1] notin Xcoords then
		    Append(~Pnts,J![ff[1],bx]);
		    Include(~Xcoords,ff[1]);
		end if;
	    end for;
	end for;
    else
	Xcoords := { K | };
	for p in RationalPoints(AffinePatch(C,1)) do
	    if Eltseq(p) ne [1,1] and p[1] notin Xcoords then
		Append(~Pnts,J![x-p[1],p[2]]);
		Include(~Xcoords,p[1]);
	    end if;
	end for;
    end if;
    return Pnts;
end intrinsic;

intrinsic Random(J::PicHypSng) -> PicHypSngElt
    {}
    C := J`Curve;
    FF := BaseRing(C);
    require Type(FF) eq FldFin :
	"Argument must be defined over a finite field.";
    f := Explode(C`HyperellipticPolynomials);
    g := (Degree(f)-1) div 2;
    P1 := ProjectiveSpace(FF,1);
    PntsP1 := RationalPoints(P1);
    m := map< C->P1 | [P2.1,P2.3] > where P2 := Ambient(C); 
    pp := J!0; 
    Z := SingularSubscheme(C);
    for i in [1..g+1] do
	Pnts := {@@};
	while #Pnts eq 0 do
	    Pnts := RationalPoints(Random(PntsP1)@@m);
	    if #Pnts ne 0 and Pnts[1] in Z then Pnts := {@@}; end if;
	end while;
	pp +:= J!Pnts[1];
    end for;
    return pp;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          Element Order                             // 
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Order(P::PicHypSngElt) -> RngIntElt
    {}
    J := Parent(P);
    C := J`Curve;
    FF := BaseRing(C);
    require Type(FF) eq FldFin :
	"Argument must be defined over a finite field.";
    f := Explode(C`HyperellipticPolynomials);
    degs := [ Degree(fac[1]) : fac in Factorization(f) ];
    g := (Degree(f)-1) div 2;
    p := #FF;
    n := LCM([ p^(2*d)-1 : d in degs ]);
    O := J!0;
    require n*P eq O : "Argument has some inexplicable order.";
    for m in Factorization(n) do
	for i in [1..m[2]] do
	    if (n div m[1])*P ne O then
		break i;
	    else
		n div:= m[1];
	    end if;
	end for;
    end for;
    assert n*P eq O;
    return n;
end intrinsic;

