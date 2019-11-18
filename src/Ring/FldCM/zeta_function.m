//////////////////////////////////////////////////////////////////////////////
//                                                                          //
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

intrinsic 'eq'(R1::RngOrdRes,R2::RngOrdRes) -> BoolElt
    {Return true if and only if the arguments are quotients
    of the same order by the same ideal.}
    return R1 cmpeq R2;
end intrinsic;

/*
intrinsic ZetaFunction(O::RngOrd,pi::RngOrdElt : ExtraPrecision := 0) -> RngSerElt
    {Given a CM order O and a Frobenius element pi, return
    the zeta function exp(sum_n=1^oo #O/(pi^n-1)/n * t^n)
    as a rational function.}
    K := NumberField(O);
    require IsCMField(K) : "Argument 1 must be an order in a CM field.";
    require Parent(pi) eq O : "Argument 2 must be an element of argument 1.";
    g := Degree(K) div 2; N := Norm(pi); bool, q := IsPower(N,g);
    require bool and q^g eq N : "Norm of argument 2 must be a g-th power of an integer.";
    e := ExtraPrecision;
    PS<t> := PowerSeriesRing(RationalField());
    PZ<x> := PolynomialRing(IntegerRing());
    // This is the zeta function of the Jacobian:
    //return Exp(&+[ Norm(K!pi^n - 1)/n * t^n : n in [1..2*g+e] ] + BigO(t^(2*g+1+e)));
    zeta := Exp(&+[ -Trace(K!pi^n)/n * t^n : n in [1..2*g+e] ] + BigO(t^(2*g+1+e)));
    den := BerlekampMassey(zeta);
    num := PZ!Eltseq(Truncate(zeta * PS!den));
    return num/den;
end intrinsic;
*/

intrinsic ZetaFunction(R::RngOrdRes,pi::RngOrdResElt : ExtraPrecision := 0) -> RngSerElt
    {Given a quotient R of a CM order O and a Frobenius element pi,
    return the zeta function exp(sum_n=1^oo |O/(pi^n-1)|/n * t^n)
    as a rational function.}
    I := Modulus(R); O := Order(I);
    K := NumberField(O); g := Degree(K) div 2;
    require IsCMField(K) : "Argument 1 must be a quotient of a CM order.";
    require Parent(pi) eq R : "Argument 2 must be an element of argument 1.";
    PS<t> := PowerSeriesRing(RationalField());
    PZ<x> := PolynomialRing(IntegerRing());
    N := Norm(I) + ExtraPrecision;
    return PZ!Eltseq(Exp(&+[ -#quo< R | pi^n - 1>/n * t^n : n in [1..N] ] + BigO(t^(N+1))));
end intrinsic;
