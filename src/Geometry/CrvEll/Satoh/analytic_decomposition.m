////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                 Satoh AGM Analytic Lifting Functions               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "modular_correspondences.m" : PhiX;

function ProductRepresentation(f,p,n)
    // f is a power series over the integers
    S := Parent(f); t := S.1;
    P := PolynomialRing(BaseRing(S)); x := P.1;
    polys := [P|];
    for i in [0..n-1] do
        m := AbsolutePrecision(f);
        vals := [ j : j in [0..m-1] | Valuation(Coefficient(f,j),p) le i ];
        g := &+[ P | Coefficient(f,j)*x^j : j in vals ];
	Append(~polys,g);
        f /:= Evaluate(g,t); 
    end for;
    return polys;
end function;

intrinsic AnalyticSatohFrobenius(p::RngIntElt,prec::RngIntElt) -> SeqEnum
    {}
    require IsPrimePower(p) : "Argument 1 must be a prime power.";
    S<x> := LaurentSeriesRing(Rationals());
    AssertAttribute(S,"Precision",prec);
    P<y> := PolynomialRing(S);
    return Roots(PhiX(p,x,y))[1][1]; 
end intrinsic;

intrinsic AnalyticSatohPowerProduct(p::RngIntElt,prec::RngIntElt) -> SeqEnum
    {Return a sequence of polynomials, the initial k
    elements of which have product which approximates
    the analytic p^i correspondence on X_0(N).}
    require IsPrimePower(p) : "Argument 1 must be a prime power.";
    return AnalyticSatohPowerProduct(p,1,prec);
end intrinsic;

intrinsic AnalyticSatohPowerProduct(
    p::RngIntElt,i::RngIntElt,prec::RngIntElt) -> SeqEnum
    {Return a sequence of polynomials, the initial k
    elements of which have product which approximates
    the analytic p^i correspondence on X_0(N).}
    require IsPrimePower(p) : "Argument 1 must be a prime power.";
    oprec := p*(i*prec+1);
    S := LaurentSeriesRing(Rationals()); x := S.1;
    AssertAttribute(S,"Precision",oprec);
    P := PolynomialRing(S); y := P.1;
    for j in [1..i] do
	// yx := Roots(PhiX(p,x,y))[1][1];
	yx := NewtonLift(PhiX(p,x,y),x^p+O(x^oprec),oprec);
        if j ne i then x := yx; end if; 
    end for;
    return ProductRepresentation(yx,p,prec);
end intrinsic;
