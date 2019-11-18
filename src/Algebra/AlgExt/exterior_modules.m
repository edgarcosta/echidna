//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        Exterior Modules                                  //
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

/* Created 22 September 1999. */

////////////////////////////////////////////////////////////////
//                                                            //
//                  Attribute declarations                    //
//                                                            //
////////////////////////////////////////////////////////////////

declare type ModExt[ModExtElt];

declare attributes ModExt:
   algebra,
   weight,
   is_full,
   basis;

declare attributes ModExtElt:
   parent,
   element;

////////////////////////////////////////////////////////////////
//                                                            //
//                   Creation functions                       //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic ExteriorModule(E::AlgExtEch,k::RngIntElt) -> ModExt
   {The submodule of kth exterior powers.}
   L := New(ModExt);
   L`algebra := E;
   L`weight := k;
   L`is_full := true;
   return L;
end intrinsic;

intrinsic ExteriorProduct(v::ModExtElt,M::ModExt) -> ModExt
   {Exterior product module.}
   E := Algebra(M);
   k := Weight(M) + Weight(v);
   L := New(ModExt);
   L`algebra := E;
   L`weight := k;
   L`is_full := false;
   L`basis := SpanningBasis(
      [ Component(E,k)![E!v,E!x] : x in Basis(M) ] );
   return L;
end intrinsic;

intrinsic ExteriorProduct(M::ModExt,v::ModExtElt) -> ModExt
   {Exterior product module.}
   return ExteriorProduct(v,M);
end intrinsic;

intrinsic ExteriorProduct(v::AlgExtEchElt,M::ModExt) -> ModExt
   {Exterior product module.}
   require IsHomogeneous(v):
      "Algebra element must be homogeneous.";
   E := Algebra(M);
   require Parent(v) eq E:
      "Incompatible exterior algebras.";
   k := Weight(M) + Weight(v);
   L := New(ModExt);
   L`algebra := E;
   L`weight := k;
   L`is_full := false;
   L`basis := SpanningBasis(
      [ Component(E,k)![v,E!x] : x in Basis(M) ] );
   return L;
end intrinsic;

intrinsic ExteriorProduct(M::ModExt,v::AlgExtEchElt) -> ModExt
   {Exterior product module.}
   return ExteriorProduct(v,M);
end intrinsic;

intrinsic ExteriorProduct(M::ModExt,N::ModExt) -> ModExt
   {The kth exterior power.}
   E := Algebra(M);
   k := Weight(M) + Weight(N);
   L := New(ModExt);
   L`algebra := E;
   L`weight := k;
   L`is_full := false;
   L`basis := SpanningBasis(
      [ Component(E,k)![E!x,E!y] : x in Basis(M), y in Basis(N) ] );
   return L;
end intrinsic;

intrinsic ExteriorPower(V::ModTupFld,k::RngIntElt) -> ModExt
   {The kth exterior power.}
   L := New(ModExt);
   L`algebra := ExteriorAlgebra(V);
   L`weight := k;
   L`is_full := true;
   return L;
end intrinsic;

intrinsic ExteriorPower(M::ModTupRng,k::RngIntElt) -> ModExt
   {The kth exterior power.}
   L := New(ModExt);
   L`algebra := ExteriorAlgebra(M);
   L`weight := k;
   L`is_full := true;
   return L;
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//                     Coercions                              //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic IsCoercible(M::ModExt,s::.) -> BoolElt, ModExt
   {}
   if Weight(M) eq 1 and
      Type(s) in {ModTupFldElt, ModTupRngElt} and
      Parent(s) eq DefiningModule(M) then
      x := New(ModExtElt);
      x`parent := M;
      x`element := Algebra(M)!s;
      return true, x;
   elif Type(s) eq ModExtElt and Parent(s) eq M then
      s`parent := M;
      return true, s;
   elif Type(s) eq AlgExtEchElt then
      if IsHomogeneous(s) and Weight(s) eq Weight(M) then
         x := New(ModExtElt);
         x`parent := M;
         x`element := s;
         return true, x;
      end if;
   elif Type(s) in {List,SeqEnum} then
      U := Universe(s);
      if Type(U) in {ModTupFld, ModTupRng} and
         U eq DefiningModule(M) and #s eq Weight(M) then
         x := New(ModExtElt);
         x`parent := M;
         x`element := Product([ Algebra(M)!y : y in s ]);
         return true, x;
      elif Type(U) eq AlgExtEch and U eq Algebra(M) and
         &+[ Weight(y) : y in s ] eq Weight(M) then
         x := New(ModExtElt);
         x`parent := M;
         x`element := Product([ Algebra(M)!y : y in s ]);
         return true, x;
      elif Type(U) eq ModExt and Algebra(U) eq Algebra(M) and
         &+[ Weight(y) : y in s ] eq Weight(M) then
         x := New(ModExtElt);
         x`parent := M;
         x`element := Product([ Algebra(M)!y : y in s ]);
         return true, x;
      end if;
   end if;
   return false, "Illegal coercion.";
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//                     Printing                               //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic Print(M::ModExt, level::MonStgElt)
   {}
   printf "Exterior power module of weight %o for %o",
      Weight(M), DefiningModule(M);
end intrinsic;

intrinsic Print(x::ModExtElt, level::MonStgElt)
   {}
   printf "%o", x`element;
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//            Membership and equality testing                 //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., M::ModExt) -> BoolElt
   {Returns true if x is in M.}
   if Type(x) eq ModExtElt then
      return Parent(x) eq M;
   end if;
   return false;
end intrinsic;

intrinsic Parent(x::ModExtElt) -> ModExt
   {}
   return x`parent;
end intrinsic;

intrinsic 'eq' (M::ModExt,N::ModExt) -> BoolElt
   {}
   return Algebra(M) eq Algebra(N) and Weight(M) eq Weight(N);
end intrinsic;

intrinsic 'eq' (x::ModExtElt,y::ModExtElt) -> BoolElt
   {}
   return Parent(x) eq Parent(y) and x`element eq y`element;
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//                Attribute Access Functions                  //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic Algebra(M::ModExt) -> AlgExtEch
   {}
   return M`algebra;
end intrinsic;

intrinsic Weight(M::ModExt) -> RngIntElt
   {}
   return M`weight;
end intrinsic;

intrinsic Weight(x::ModExtElt) -> RngIntElt
   {The weight of x.}
   return Weight(Parent(x));
end intrinsic;

intrinsic DefiningSpace(M::ModExt) -> ModTupRng
   {}
   return DefiningModule(M);
end intrinsic;

intrinsic DefiningModule(M::ModExt) -> ModTupRng
   {}
   return DefiningModule(Algebra(M));
end intrinsic;

intrinsic BaseRing(M::ModExt) -> Rng
   {}
   return BaseRing(Algebra(M));
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//         Functionality, arithmetic operations, etc.         //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic '+' (x::ModExtElt,y::ModExtElt) -> ModExtElt
   {}
   M := Parent(x);
   require Parent(y) eq M: "Elements have different parents.";
   z := New(ModExtElt);
   z`parent := M;
   z`element := x`element + y`element;
   return z;
end intrinsic;

intrinsic '*' (x::ModExtElt,y::ModExtElt) -> AlgExtEchElt
   {}
   E := Algebra(Parent(x));
   require Algebra(Parent(y)) eq E:
      "Elements have different parent algebras.";
   z := New(ModExtElt);
   z`parent := Component(Parent(x),Weight(x)+Weight(y));
   z`element := x`element * y`element;
   return z;
end intrinsic;

intrinsic IsFull(M::ModExt) -> BoolElt
   {Returns true if M is the full space of weight k.}
   return M`is_full;
end intrinsic;

function Choose(S,r)
    if (r gt #S) or (r lt 0) then
	return [ Universe([ Universe(S) | ]) | ];
    end if;
    return [ [ S[i] : i in I ] : I in subseqs ]
	where subseqs := Sort([ [ i : i in I] : I in subsets ])
	where subsets := Subsets(SequenceToSet([1..#S]),r);
end function;

intrinsic Basis(M::ModExt) -> SeqEnum
   {The basis for M.}
   B := Basis(DefiningModule(M));
   if IsFull(M) then
       return [ M!S : S in Choose(B,Weight(M)) ];
   end if;
   return M`basis;
end intrinsic;

intrinsic Dimension(M::ModExt) -> RngIntElt
   {The rank of the space M.}
   if IsFull(M) then
      return Binomial(
         Dimension(DefiningModule(M)), Weight(M) );
   else
      return #Basis(M);
   end if;
end intrinsic;

intrinsic Norm(x::ModExtElt) -> RngElt
   {The determinant norm of x with respect to the inner product
   on the defining quadratic space.}
   return Determinant(x);
end intrinsic;

intrinsic Determinant(x::ModExtElt) -> RngElt
   {The determinant of x with respect to the inner product
   on the defining quadratic space.}
   V := DefiningModule(Parent(x));
   R := BaseRing(Parent(x));
   k := Weight(x);
   S := (x`element)`element;
   return &+[ a[1]*b[1]*Determinant(
       MatrixAlgebra(R,k)![ InnerProduct(V.i,V.j) : i, j in a[2] ]) : a, b in S ];
end intrinsic;

intrinsic InnerProduct(x::ModExtElt,y::ModExtElt) -> RngElt
   {The determinant inner product.}
   V := DefiningModule(Parent(x));
   R := BaseRing(Parent(x));
   k := Weight(x);
   S := (x`element)`element;
   T := (y`element)`element;
   return &+[ R | a[1]*b[1]*Determinant(
       MatrixAlgebra(R,k)![ InnerProduct(V.i,V.j) : i in a[2], j in b[2] ]) : a in S, b in T ];
end intrinsic;

intrinsic QuadraticModule(M::ModExt) -> ModTupFld
   {The quadratic module of M with respect to the determinant form.}
   B := Basis(M);
   R := BaseRing(M);
   r := Dimension(M);
   A := MatrixAlgebra(R,r)![ InnerProduct(x,y) : x, y in B ];
   return QuadraticSpace(A);
end intrinsic;

intrinsic QuadraticSpace(M::ModExt) -> ModTupFld
   {The quadratic space of M with respect to the determinant form.}
   return QuadraticModule(M);
end intrinsic;

intrinsic SpanningBasis(B::[ModExtElt])-> SeqEnum
   {A reduced basis spanned by B.}
   M := Universe(B);
   E := Algebra(M);
   R := BaseRing(M);
   Supp := [ s : s in &join[ { a[2] : a in (x`element)`element } : x in B ] ];
   V := RSpace(R,#Supp);
   B1 := [ V | ];
   for x in B do
      v := V!0;
      for a in (x`element)`element do
         v[Index(Supp,a[2])] := a[1];
      end for;
      Append(~B1,v);
   end for;
   B1 := Basis(sub< V | B1 >);
   return [ M!Summation([ v[j]*Product([ E.i : i in Supp[j]]) : j in [1..#Supp] | v[j] ne 0 ]) : v in B1 ];
end intrinsic;

intrinsic Summation(S::[ModExtElt]) -> ModExtElt
   {}
   E := Universe(S);
   z := E!0;
   for i in [1..#S] do
      z := z + S[i];
   end for;
   return z;
end intrinsic;

