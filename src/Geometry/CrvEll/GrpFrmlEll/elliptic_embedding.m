//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Formal Group arithmetic on Elliptic Curves                              //
//  Copyright (C) 2004 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
Make this more intrinsic, and expression as embeddings of the formal group on
the elliptic curve, and on its Kummer curve.  See also the file morphisms.m.
*/

intrinsic FormalRelation(xE::RngSerElt,xF::RngSerElt) -> RngSerElt
    {}
    prec := Min(RelativePrecision(xE),RelativePrecision(xF))-2;
    PS := Parent(xE); z := PS.1;
    tE := 1/xE;
    xF := xF*tE-1;
    fz := PS!1;
    tEk := PS!1;
    for i in [1..prec div 2] do
	tEk *:= tE;
	ck := Coefficient(xF,2*i);
	fz +:= ck*z^i;
	xF +:= -ck*tEk;
    end for;
    return fz + O(z^(prec+1));
end intrinsic;

intrinsic FormalReversion(E::CrvEll,F::CrvEll,prec::RngIntElt) -> RngSerElt
    {A power series f such that x_F = x_E*f(1/x_E).}
    tE := 1/FormalGroupExpansion(E,2*prec);
    tF := FormalGroupExpansion(F,2*prec)*tE;
    PS := Parent(tE); z := PS.1;
    fz := PS!1;
    tF +:= -1;
    tEk := tE;
    for i in [1..prec] do
	ck := Coefficient(tF,2*i);
	tF +:= -ck*tEk;
	fz +:= ck*z^i;
	tEk *:= tE;
    end for;
    return fz + O(z^(prec+1));
end intrinsic;

intrinsic FormalGroupExpansion(E::CrvEll,N::RngIntElt) -> RngSer, RngSer
   {Returns the formal group power series x(z) of E, followed by
   the power series y(z) = -x(z)/z. Express this as a map from the
   formal group sending z -> (x(z),y(z)) on the elliptic curve.}
   R := BaseRing(E);
   RPol<c> := PolynomialAlgebra(R);
   KPow<z> := LaurentSeriesRing(RPol);
   a1,a2,a3,a4,a6 := Explode(aInvariants(E));
   xz := z^-2 - a1*z^-1 - a2-a3*z + (-a3*a1-a4)*z^2 +
      (-a3*a1^2-a4*a1-a3*a2)*z^3 +
      (-a3*a1^3-a4*a1^2-2*a3*a2*a1+(-a4*a2+(-a3^2-a6)))*z^4 +
      (-a3*a1^4-a4*a1^3-3*a3*a2*a1^2 + (-2*a4*a2+(-3*a3^2-2*a6))*a1 + (-a3*a2^2-2*a4*a3))*z^5 + c*z^6 + O(z^7);
   for k in [6..N] do
      s := Numerator(Coefficient(Evaluate(Polynomial(E),[xz,-xz/z,1]),k-4));
      c0 := -Coefficient(s,0)/Coefficient(s,1);
      xz := Truncate(xz + O(z^(k))) + c0*z^(k) + c*z^(k+1) + O(z^(k+2));
   end for;
   xz := (Truncate(xz + O(z^(N+1))) + O(z^(N+1)));
   xc := Coefficients(xz);
   xc := [ Evaluate(xc[i],0) : i in [1..#xc] ];
   RPow<z> := LaurentSeriesRing(R);
   xz := &+[ xc[i]*z^(i-3) : i in [1..#xc] ] + O(z^(N+1));
   yz := -xz/z;
   return xz, yz;
end intrinsic;

intrinsic FormalEmbedding(E::CrvEll : Precision := 100) -> Map
   {}
   n := Precision;
   R := BaseRing(E);
   PS := LaurentSeriesRing(R);
   z := PS.1;
   a1, a2, a3, a4, a6 := Explode(aInvariants(E));
   xz := z^-2 - a1*z^-1 - a2 - a3*z - (a3*a1 + a4)*z^2 -
      (a3*a1^2 + a4*a1 + a3*a2)*z^3 +
      (-a3*a1^3-a4*a1^2-2*a3*a2*a1+(-a4*a2+(-a3^2-a6)))*z^4 +
      (-a3*a1^4-a4*a1^3-3*a3*a2*a1^2 +
         (-2*a4*a2+(-3*a3^2-2*a6))*a1 + (-a3*a2^2-2*a4*a3))*z^5 + O(z^n);
   PR := PolynomialRing(PS);
   x := PR.1;
   F := z^2*x^3 + (z^2*a2 + z*a1 - 1)*x^2 + (z^2*a4 + z*a3)*x + z^2*a6;
   DF := Derivative(F);
   while true do
      Fz := Evaluate(F,xz);
      if RelativePrecision(Fz) eq 0 then break; end if;
      DFz := Evaluate(DF,xz);
      xz +:= -Fz/DFz;
   end while;
   yz := -xz/z;
   K := FunctionField(E);
   return hom< K -> PS | f :-> Evaluate(RationalFunction(f),[xz,yz]) >;
end intrinsic;

