////////////////////////////////////////////////////////////////////
//                                                                //
//                    SQUARES AND SQUARE ROOTS                    //
//                 IN BINARY QUADRATIC CLASS GROUPS               //
//                         David Kohel                            //
//                    Last modified April 2000                    //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic IsSquare(f::QuadBinElt) -> BoolElt
   {Returns true if f is in the principal genus.} 
   f := Reduction(f);
   G0 := Genus(Lattice(Parent(f)!1));
   G1 := Genus(Lattice(f));
   return G0 eq G1;
end intrinsic;

intrinsic SquareRoot(f::QuadBinElt) -> BoolElt
   {A representative form whose square is f, well-defined 
   modulo the 2-torsion subgroup.}

   Q := Parent(f);
   // Trivial case:
   if f eq Q!1 then return f; end if;
   require IsSquare(f) : "Argument 1 is not a square";
   // Force the computation of class number...
   G, m := ClassGroup(Q);
   h := ClassNumber(Q : Al := "ClassGroup");
   r := Order(f);
   if IsOdd(r) then
      return f^InverseMod(2,r);
   else
      r1 := r div 2^Valuation(r,2);
      r2 := r div r1;
      // A bug in InverseMod:
      if r1 eq 1 then
         g1 := Q!1;
      else
         g1 := f^CRT([InverseMod(2,r1),0],[r1,r2]);
      end if;
      f2 := f^CRT([0,1],[r1,r2]);
   end if;
   h := #G;   
   h1 := h div 2^Valuation(h,2);
   H := sub< G | [ 2*h1*G.i : i in [1..Ngens(G)] ] >;
   e2 := [ Valuation(Order(G.i),2) : i in [1..Ngens(G)] ];
   H2 := sub< G | [ 2^Max(e2[i]-1,1)*h1*G.i : i in [1..Ngens(G)] ] >;
   T2 := [ f2 ];
   for i in [1..Valuation(r2,2)-1] do
      Append(~T2,T2[#T2]^2);
   end for;
   x2 := G!0;
   for i in [1..#T2] do
      x2 := [ x2 + G!x : x in H2 | m(x2 + G!x) eq T2[#T2-i+1] ][1]; 
      s2 := Eltseq(x2);
      x2 := G![ s2[i] div 2 : i in [1..#s2] ];
   end for;
   g2 := m(x2);
   return g1*g2;
end intrinsic;

