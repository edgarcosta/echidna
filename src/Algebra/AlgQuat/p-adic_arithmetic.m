//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2014 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic pAdicRandomIsotropicElement(
    O::AlgQuatOrd[RngInt],p::RngIntElt,n::RngIntElt : Bound := 8) -> AlgQuatOrdElt
    {A random element x of I of norm zero mod p^n.}
    // Input: I quaternion order or ideal, p an unramified 
    // prime, and n a precision.
    // Output: an element x of I such that Nr(x)/Nr(I) = 0 mod p^n 
    ZZ := IntegerRing();
    N := Discriminant(QuaternionAlgebra(O));
    require N mod p ne 0 : "Argument 2 must be an unramified prime of argument 1.";
    repeat
        x := RandomElement(O : Bound := Bound, Primitive);
        D := Trace(x)^2 - 4*Norm(x);
    until KroneckerSymbol(D,p) eq 1;
    P := PolynomialRing(FiniteField(p)); t := P.1;
    a := ZZ!Random(Roots(t^2 - Trace(x)*t + Norm(x)))[1];
    function bal_mod(a, m)
        r := a mod m;
        if 2*r gt m then
           r := r - m;
        end if;
        return r;
    end function;
    return O![ bal_mod(ZZ!c,p^n) : c in Eltseq((x-a)^n) ];
end intrinsic;

intrinsic pAdicRandomIsotropicElement(
    I::AlgQuatOrdIdl[RngInt],p::RngIntElt,n::RngIntElt :
    Bound := 8, OrderSide := "Right") -> AlgQuatOrdElt
    {A random element x of I of norm zero mod N(I)*p^n.}
    // Input: I quaternion order or ideal, p an unramified
    // prime, and n a precision.
    // Output: an element x of I such that Nr(x)/Nr(I) = 0 mod p^n
    require Type(OrderSide) eq MonStgElt and OrderSide in {"Right","Left"}:
        "The parameter \"OrderSide\" must be \"Right\" or \"Left\".";
    if OrderSide eq "Right" then
        O := RightOrder(I);
    else
        O := LeftOrder(I);
    end if;
    // This makes the element x commute, in the sense that I x = x I.
    //O := RightOrder(I) meet LeftOrder(I);
    ZZ := IntegerRing();
    N := Discriminant(QuaternionAlgebra(O));
    require N mod p ne 0 : "Argument 2 must be an unramified prime of argument 1.";
    x := pAdicRandomIsotropicElement(O,p,n);
    q := Norm(I);
    r := Valuation(q,p);
    for z in Generators(I) do
        if Valuation(Norm(z),p) eq r then
            if OrderSide eq "Right" then
                return O!(z*x);
            else
                return O!(x*z);
            end if;
        end if;
    end for;
    if OrderSide eq "Right" then
        return O!(RandomElement(I)*x);
    else
        return O!(x*RandomElement(I));
    end if;
end intrinsic;

