//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      Exterior Algebras                                   //
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

declare type AlgExtEch[AlgExtEchElt];

declare attributes AlgExtEch:
   quadratic_module,
   generator_labels,
   components;

declare attributes AlgExtEchElt:
   parent,
   element;

////////////////////////////////////////////////////////////////
//                                                            //
//                   Creation functions                       //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic ExteriorAlgebra(V::ModTupFld) -> AlgExtEch
   {The exterior algebra.}
   E := New(AlgExtEch);
   E`quadratic_module := V;
   E`generator_labels := [ "$." cat IntegerToString(i) :
      i in [1..Dimension(V)] ];
   E`components := [ ];
   return E;
end intrinsic;

intrinsic ExteriorAlgebra(V::ModTupRng) -> AlgExtEch
   {The exterior algebra.}
   dim := Dimension(V);
   E := New(AlgExtEch);
   E`quadratic_module := V;
   E`generator_labels := [ "$." cat IntegerToString(i) : i in [1..dim] ];
   E`components := [ ];
   return E;
end intrinsic;

intrinsic AssignNames(~E::AlgExtEch, S::[MonStgElt])
   {Assign names to generating elements.}
   n := Dimension(DefiningModule(E));
   require #S eq n: "Argument 2 must have length", n;
   E`generator_labels := S;
end intrinsic;

intrinsic Name(E::AlgExtEch,i::RngIntElt) -> AlgExtEchElt
   {The ith basis element.}
   require 1 le i and i le Dimension(DefiningModule(E)):
      "Invalid argument.";
   return E.i;
end intrinsic;

intrinsic '.'(E::AlgExtEch,i::RngIntElt) -> AlgExtEchElt
   {The ith basis element.}
   V := DefiningModule(E);
   n := Dimension(V);
   require 1 le i and i le Dimension(DefiningModule(E)):
      "Invalid argument.";
   S := [ Zero(BaseRing(E)) : j in [1..n] ];
   S[i] := 1;
   return E!(V!S);
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//                     Coercions                              //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic IsCoercible(E::AlgExtEch,s::.) -> BoolElt, AlgExtEch
   {}
   if Type(s) eq RngIntElt then
      x := New(AlgExtEchElt);
      x`parent := E;
      x`element := [ <BaseRing(E)!s,[]> ];
      return true, x;
   elif Parent(s) cmpeq BaseRing(E) then
      x := New(AlgExtEchElt);
      x`parent := E;
      x`element := [ <s,[]> ];
      return true, x;
   elif Type(s) eq AlgExtEchElt and Parent(s) eq E then
      return true, s;
   elif Type(s) eq ModExtElt and Algebra(Parent(s)) eq E then
      return true, s`element;
   elif Type(s) in {ModTupFldElt, ModTupRngElt} and
      Parent(s) eq DefiningSpace(E) then
      dim := Degree(Parent(s));
      x := New(AlgExtEchElt);
      x`parent := E;
      x`element := [ <s[i],[i]> : i in [1..dim] | s[i] ne 0 ];
      return true, x;
   end if;
   return false, "Illegal coercion.";
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//                     Printing                               //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic Print(E::AlgExtEch, level::MonStgElt)
   {}
   printf "Exterior algebra of %o", DefiningSpace(E);
end intrinsic;

intrinsic Print(x::AlgExtEchElt, level::MonStgElt)
   {}
   E := Parent(x);
   plus := "";
   for a in x`element do
      if #a[2] gt 0 and a[1] eq 1 then
         printf plus;
         naked := true;
      elif #a[2] gt 0 and a[1] eq -1 then
         printf "-" cat plus;
         naked := true;
      else
         printf plus cat "%o", a[1];
         naked := false;
      end if;
      for i in [1..#a[2]] do
         if i ne 1 or not naked then
            printf "*";
         end if;
         printf "%o", GeneratorString(E,a[2][i]);
      end for;
      plus := " + ";
   end for;
   if #x`element eq 0 then
      printf "0";
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//            Membership and equality testing                 //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., E::AlgExtEch) -> BoolElt
   {Returns true if x is in C.}
   if Type(x) eq AlgExtEchElt then
      return Parent(x) eq E;
   elif Type(x) in {ModTupFldElt, ModTupRngElt} then
      return Parent(x) eq DefiningSpace(E);
   end if;
   return false;
end intrinsic;

intrinsic Parent(x::AlgExtEchElt) -> AlgExtEch
   {}
   return x`parent;
end intrinsic;

intrinsic 'eq' (E::AlgExtEch,F::AlgExtEch) -> BoolElt
   {}
   return DefiningModule(E) eq DefiningModule(F);
end intrinsic;

intrinsic 'eq' (x::AlgExtEchElt,y::AlgExtEchElt) -> BoolElt
   {}
   return Parent(x) eq Parent(y) and 
          x`element eq y`element;
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//                Attribute Access Functions                  //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic DefiningModule(E::AlgExtEch) -> Rng
   {}
   return E`quadratic_module;
end intrinsic;

intrinsic DefiningSpace(E::AlgExtEch) -> Rng
   {}
   return DefiningModule(E);
end intrinsic;

intrinsic GeneratorString(E::AlgExtEch,k::RngIntElt) -> MonStgElt
   {}
   return (E`generator_labels)[k];
end intrinsic;

intrinsic Component(E::AlgExtEch,k::RngIntElt) -> MonStgElt
   {}
   if not IsDefined(E`components,k) then
      (E`components)[k] := ExteriorModule(E,k);
   end if;
   return (E`components)[k];
end intrinsic;

intrinsic BaseField(E::AlgExtEch) -> Rng
   {}
   return BaseField(DefiningModule(E));
end intrinsic;

intrinsic BaseRing(E::AlgExtEch) -> Rng
   {}
   return BaseRing(DefiningModule(E));
end intrinsic;

intrinsic IsHomogeneous(x::AlgExtEchElt) -> BoolElt
   {}
   S := x`element;
   if #S eq 0 then
      return true;
   end if;
   return &and[ #S[1][2] eq #S[j][2] : j in [1..#S] ];
end intrinsic;

intrinsic Weight(x::AlgExtEchElt) -> RngIntElt
   {The weight of a homogeneous exterior algebra element.}
   require IsHomogeneous(x): "Element is not homogeneous.";
   return #(x`element)[1][2];
end intrinsic;

////////////////////////////////////////////////////////////////
//                                                            //
//         Functionality, arithmetic operations, etc.         //
//                                                            //
////////////////////////////////////////////////////////////////

intrinsic Zero(E::AlgExtEch) -> AlgExtEchElt
   {}
   x := New(AlgExtEchElt);
   x`parent := E;
   x`element := [ ];
   return x;
end intrinsic;

function IsAscending(S)
   for i in [1..#S-1] do
      if S[i] ge S[i+1] then
         return false, i;
      end if;
   end for;
   return true, 0;
end function;

function AdditiveReduction(expanded_elt)
   reduced_elt := [ ];
   for wrd in { a[2] : a in expanded_elt } do
      a := &+[ a[1] : a in expanded_elt | a[2] eq wrd ];
      if a ne 0 then
         Append(~reduced_elt,<a,wrd>);
      end if;
   end for;
   return reduced_elt;
end function;

function WordReduction(word_elt)
   reduced_elt := [ ];
   changed := false;
   for a in word_elt do
      yes, i := IsAscending(a[2]);
      if yes then
         Append(~reduced_elt,a);
      else
         if a[2][i] ne a[2][i+1] then
            s := [ a[2][j] : j in [1..i-1] ] cat
                 [ a[2][i+1], a[2][i] ] cat
                 [ a[2][j] : j in [i+2..#a[2]] ];
            reduced_elt cat:= [<-a[1],s>];
            changed := true;
         end if;
      end if;
   end for;
   if changed then
      return WordReduction(reduced_elt);
   else
      return reduced_elt;
   end if;
end function;

intrinsic '+' (x::AlgExtEchElt,y::AlgExtEchElt) -> AlgExtEchElt
   {}
   E := Parent(x);
   require Parent(y) eq E: "Elements have different parents.";
   z := New(AlgExtEchElt);
   z`parent := E;
   z`element := AdditiveReduction(x`element cat y`element);
   return z;
end intrinsic;

intrinsic '-' (x::AlgExtEchElt) -> AlgExtEchElt
   {}
   z := New(AlgExtEchElt);
   z`parent := Parent(x);
   z`element := [ <-a[1],a[2]> : a in x`element ];
   return z;
end intrinsic;

intrinsic '-' (x::AlgExtEchElt,y::AlgExtEchElt) -> AlgExtEchElt
   {}
   E := Parent(x);
   require Parent(y) eq E: "Elements have different parents.";
   z := New(AlgExtEchElt);
   z`parent := E;
   z`element := AdditiveReduction(x`element cat (-y)`element);
   return z;
end intrinsic;

intrinsic '*' (x::RngElt,y::AlgExtEchElt) -> AlgExtEchElt
   {}
   R := BaseRing(Parent(y));
   if Type(x) eq RngIntElt then
      x := R!x;
   end if;
   require Parent(x) eq R: "Scalar is not in coefficient ring.";
   z := New(AlgExtEchElt);
   z`parent := Parent(y);
   z`element := [ <x*a[1],a[2]> : a in y`element ];
   return z;
end intrinsic;

intrinsic '*' (x::AlgExtEchElt,y::RngElt) -> AlgExtEchElt
   {}
   return y*x;
end intrinsic;

intrinsic '*' (x::AlgExtEchElt,y::AlgExtEchElt) -> AlgExtEchElt
   {}
   E := Parent(x);
   require Parent(y) eq E: "Elements have different parents.";
   z := New(AlgExtEchElt);
   z`parent := E;
   z`element := WordReduction(AdditiveReduction(
       [ <a[1]*b[1],a[2] cat b[2]> : a in x`element, b in y`element ] ) );
   return z;
end intrinsic;

intrinsic Product(S::[AlgExtEchElt]) -> AlgExtEchElt
   {}
   E := Universe(S);
   z := E!1;
   for i in [1..#S] do
      z := z*S[i];
   end for;
   return z;
end intrinsic;

intrinsic Summation(S::[AlgExtEchElt]) -> AlgExtEchElt
   {}
   E := Universe(S);
   z := E!0;
   for i in [1..#S] do
      z := z + S[i];
   end for;
   return z;
end intrinsic;

intrinsic '^' (x::AlgExtEchElt,k::RngIntElt) -> AlgExtEchElt
   {}
   return Zero(Parent(x));
end intrinsic;

