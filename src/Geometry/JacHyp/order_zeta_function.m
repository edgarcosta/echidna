//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//         Copyright (C) 2010 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic MaximalOrderTorsionSplittingDegree(
    zeta::RngUPolElt[RngInt],l::RngIntElt) -> RngIntElt, RngIntElt
    {}
    require IsPrime(l) : "Argument 2 must be prime.";
    return MaximalOrderTorsionSplittingDegree(zeta,l,1);
end intrinsic;

intrinsic MaximalOrderTorsionSplittingDegree(
    zeta::RngUPolElt[RngInt],l::RngIntElt,n::RngIntElt) -> RngIntElt, RngIntElt
    {The extension degree over which the l^n-torsion subgroup splits completely
    for an abelian variety with Frobenius charpoly chi (relative to a finite
    field k of q elements) and maximal endomorphism ring. The second return value
    is the cardinality q of the base field k.}
    g := Degree(zeta) div 2;
    bool, q := IsPower(Coefficient(zeta,0),g);
    require bool :
	"Argument 1 must be the characteristic polynomial of Frobenius for a curve over a finite field.";
    bool, p := IsPrimePower(q);
    require bool :
	"Argument 1 must be the characteristic polynomial of Frobenius for a curve over a finite field.";
    require IsPrime(l) : "Argument 2 must be prime";
    K<pi> := NumberField(zeta);
    O := MaximalOrder(K);
    prms := Decomposition(O,l);
    e := 1;
    r := 1;
    for pp in prms do
	k, f := ResidueClassField(pp[1]);
	pi_i := f(O!pi);
	if pi_i ne 0 then
	    r := LCM(Order(pi_i),r);
	elif l ne p then
	    assert false;
	    qi_i := f(O!(q/pi));
	    if qi_i ne 0 then
		r := LCM(Order(qi_i),r);
	    end if;
	end if;
	e := LCM(pp[2],e);
    end for;
    ZZ := Integers();
    pi_r := pi^r;
    R, f := quo< O | l^n >;
    if l ne p then
	zero := f(pi_r) eq R!1;
    else
	zero := f(pi_r*(pi_r-1)) eq 0;
    end if;
    k := 0;
    while not zero do
	k +:= 1;
	pi_r := pi_r^l;
	if l ne p then
	    zero := f(pi_r) eq R!1;
	else
	    zero := f(pi_r*(pi_r-1)) eq 0;
	end if;
    end while;
    return r*l^k, q;
end intrinsic;

intrinsic MaximalOrderTorsionSplittingField(
    zeta::RngUPolElt[RngInt],l::RngIntElt) -> FldFin, RngIntElt, FldFin
    {}
    require IsPrime(l) : "Argument 2 must be prime.";
    return MaximalOrderTorsionSplittingField(zeta,l,1);
end intrinsic;

intrinsic MaximalOrderTorsionSplittingField(
    zeta::RngUPolElt[RngInt],l::RngIntElt,n::RngIntElt) -> FldFin, RngIntElt, FldFin
    {The field over which the l^n-torsion subgroup splits completely for an
    abelian variety with Frobenius charpoly chi (relative to a finite field k)
    and maximal endomorphism ring. The second return value is the degree of
    the extension, and the third is the base field k.}
    deg, q := MaximalOrderTorsionSplittingDegree(zeta,l,n);
    FF := FiniteField(q); // Induce standard small field so it is not overwritten by nonstandard one.
    KK := FiniteField(q^deg);
    Embed(FF,KK);
    return KK, deg, FF; // and return FF so that it is not discarded.
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic FrobeniusOrder(pi::RngOrdElt,n::RngIntElt) -> RngIntElt
    {Given a Frobenius element pi in an order O, returns the degree r
    such that pi^r = 1 mod nO.}
    require false: "Not implemented error.";
    O := Parent(pi);
    require IsMaximal(O) : "Argument 1 must be maximal (not implemented error).";
    require GCD(Norm(pi),n) eq 1 : "Arguments 1 and 2 must be coprime.";
    bool, p, r := IsPrimePower(n);
    if not bool then
	return LCM([ FrobeniusOrder(pi,pp[1]^pp[2]) : pp in Factorization(n) ]);
    end if;
    prms := [ pp[1] : pp in Factorization(ideal< O | p >) ];
    rr := 1;
    for pp in prms do
	kp, mp := quo< O | pp[1] >;
	rp := Order(mp(pi));
	ep := Valuation(pi,pp);
	if ep gt 1 then
	    Rp, sp := Completion(O,pp);
	    pi_p := sp(pi);
	    while Valuation(pi_p^rp - 1) lt ep do
		rp *:= p;
	    end while;
	end if;
	rr := LCM(rr,rp);
    end for;
    return rr;
end intrinsic;

function RationalFunctionToPowerSeries(zeta,prec)
    R := BaseRing(Parent(zeta));
    S := PowerSeriesRing(R); t := S.1;
    zeta_num := Evaluate(Numerator(zeta),t + O(t^(prec)));
    zeta_den := Evaluate(Denominator(zeta),t + O(t^(prec)));
    return zeta_num/zeta_den;
end function;

intrinsic ZetaFunctionConvolutionProduct(
    zeta1::FldFunRatUElt,zeta2::FldFunRatUElt) -> FldFunRatUElt
    {...}
    FT := Parent(zeta1);
    deg1 := Degree(zeta1);
    deg2 := Degree(zeta2);
    prec := 2 * deg1 * deg2;
    require FT cmpeq Parent(zeta2) : "Arguments 1 and 2 must have the same parent.";
    R := BaseRing(FT);
    S := PowerSeriesRing(R); t := S.1;
    P := PolynomialRing(R); T := P.1;
    z1 := RationalFunctionToPowerSeries(zeta1,prec);
    require Coefficient(z1,0) eq 1 :
	"Argument 1 must have power series expansion of the form 1 + t*p(t).";
    d1 := t*Derivative(z1)/z1;
    z2 := RationalFunctionToPowerSeries(zeta2,prec);
    require Coefficient(z2,0) eq 1 :
	"Argument 2 must have power series expansion of the form 1 + t*p(t).";
    d2 := t*Derivative(z2)/z2;
    // The convolution product:
    d3 := [ (Coefficient(d1,i) * Coefficient(d2,i)) : i in [1..prec-1] ];
    z3 := Exp(&+[ (d3[i]/i)*t^i : i in [1..prec-1] ] + O(t^(prec)));
    if z3 eq 1 then return FT!1; end if;
    g3, d3 := BerlekampMassey(z3);
    g3 := P!g3;
    f3 := S!z3 * Evaluate(g3,t);
    assert Coefficient(f3,d3) eq 0;
    f3 := Polynomial([ Coefficient(f3,i) : i in [0..d3] ]);
    return FT!f3/FT!g3;
end intrinsic;
