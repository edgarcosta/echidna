freeze;
////////////////////////////////////////////////////////////////////
//                                                                //  
//                         Local Artin Rings                      //
//                            David Kohel                         // 
//                                                                // 
////////////////////////////////////////////////////////////////////

intrinsic LocalRing(R::RngOrdRes) -> RngPad
   {}
   I := Modulus(R);
   O := Order(I);
   N := Norm(I);
   val, p := IsPrimePower(N);
   require val : "Argument must be a local ring.";
   P := I + ideal< O | p >;
   n := Valuation(N,p) div Degree(P);
   val, p := IsPrimePower(Norm(P));
   f := DefiningPolynomial(O); 
   S := LocalRing(p,f,n);
   return S, hom< R -> S | x :-> S!Eltseq(O!x) >;
end intrinsic;
