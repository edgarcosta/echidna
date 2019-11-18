////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                 AGM-X0(N) Analytic Lifting Functions               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

import "modular_correspondences.m" : PhiX0;

function ProductRepresentation(f,p,n)
    // f is a power series over the integers
    S := Parent(f); t := S.1;
    P := PolynomialRing(BaseRing(S)); x := P.1;
    polys := [P|];
    for i in [0..n-1] do
        m := AbsolutePrecision(f);
        vals := [ j : j in [0..m-1] |
            Valuation(Coefficient(f,j),p) le i ];
        g := &+[ Coefficient(f,j)*x^j : j in vals ];
        Append(~polys,g);
        f /:= Evaluate(g,t); 
    end for;
    return polys;
end function;

intrinsic AnalyticAGMFrobenius(N::RngIntElt,prec::RngIntElt) -> SeqEnum
    {}
    bool, p := IsPrimePower(N);
    S<x> := LaurentSeriesRing(Rationals());
    AssertAttribute(S,"Precision",prec);
    P<y> := PolynomialRing(S);
    return Roots(PhiX0(N,p,x,y))[1][1]; 
end intrinsic;

intrinsic AnalyticAGMPowerProduct(N::RngIntElt,prec::RngIntElt) -> SeqEnum
    {Return a sequence of polynomials, the initial k
    elements of which have product which approximates
    the analytic p^i correspondence on X_0(N).}
    bool, p := IsPrimePower(N);
    require bool : "Argument 1 must be a prime power.";
    return AnalyticAGMPowerProduct(N,1,prec);
end intrinsic;

intrinsic AnalyticAGMPowerProduct(
    N::RngIntElt,i::RngIntElt,prec::RngIntElt) -> SeqEnum
    {Return a sequence of polynomials, the initial k
    elements of which have product which approximates
    the analytic p^i correspondence on X_0(N).}
    bool, p := IsPrimePower(N);
    require bool : "Argument 1 must be a prime power.";
    S<x> := LaurentSeriesRing(Rationals());
    AssertAttribute(S,"Precision",N*(i*prec+1));
    P<y> := PolynomialRing(S);
    for j in [1..i] do
        yx := Roots(PhiX0(N,p,x,y))[1][1];
        if j ne i then x := yx; end if; 
    end for;
    return ProductRepresentation(yx,p,prec);
end intrinsic;
