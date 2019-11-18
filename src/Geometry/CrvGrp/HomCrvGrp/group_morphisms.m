//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   Singular Cubic Group Morphisms                         //
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

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Attribute declarations                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare type HomCrvGrp[MapCrvGrp];

declare attributes HomCrvGrp:
   Domain,
   Codomain;

declare attributes MapCrvGrp:
   Parent,
   RationalMaps,       // defining sequence of rational or polynomials
   InfiniteLocus,      // locus of morphism which goes to infinity
   IsProjective;       // projective or affine image

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Creation Functions                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic End(C::CrvGrp) -> HomCrvGrp
   {The endomophism ring of C.}
   return Hom(C,C);
end intrinsic;

intrinsic Hom(C::CrvGrp,D::CrvGrp) -> HomCrvGrp
   {The module of homomorphisms C -> D.}
   H := New(HomCrvGrp);
   H`Domain := C;
   H`Codomain := D;
   return H;
end intrinsic;

intrinsic Identity(H::HomCrvGrp) -> MapCrvGrp
   {The identity endomorphism of C.}
   require H`Domain eq H`Codomain :
      "Argument must be a ring of endomorphisms.";
   return H!1;
end intrinsic;

intrinsic IsCoercible(H::HomCrvGrp,S::.) -> MapCrvGrp
   {}
   if Category(S) eq MapCrvGrp and Parent(S) eq H then
      return true, S;
   elif Category(S) eq RngIntElt then
      if S eq 0 then
         f := New(MapCrvGrp);
         f`Parent := H;
         f`Coordinates := [ 0 : k in [1..Rank(H)] ];
         return true, f;
      elif Codomain(H) eq Domain(H) then
         f := New(MapCrvGrp);
         f`Parent := H;
         f`Coordinates := [S] cat [0:k in [2..Rank(H)]];
         return true, f;
      end if;
   elif Category(S) eq SeqEnum then
      if Category(Universe(S)) eq RngMPol then
         require #S eq 3 :
            "Morphism must be defined by three defining polynomials";
         f := New(MapCrvGrp);
         f`Parent := H;
         f`RationalMaps := S;
         return true, f;
      elif Category(Universe(S)) eq RngInt then
         require #S eq Rank(H) : "Morphism is defined by ", Rank(H), " sequence coordinates";
         f := New(MapCrvGrp);
         f`Parent := H;
         f`Coordinates := S;
         return true, f;
      end if;
   end if;
   return false, "Invalid coercion";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             Printing                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

/*
intrinsic Print(H::HomCrvGrp, level::MonStgElt)
   {}
   C := H`Domain;
   D := H`Codomain;
   if C eq D then
      printf "Endomomorphism ring of %o", C;
   else
      printf "Module of homomorphisms from:\n%o\nto:\n%o", C, D;
   end if;
end intrinsic;
*/

intrinsic AssignNames(~H::HomCrvGrp, S::[MonStgElt])
   {Assign names to generating elements.}
   n := Rank(H);
   if Domain(H) cmpeq Codomain(H) then
      S := [ "" ] cat S;
   end if;
   require #S eq n: "Argument 2 must have length", n;
   H`GeneratorLabels := S;
end intrinsic;

intrinsic Name(H::HomCrvGrp,i::RngIntElt) -> MapCrvGrp
   {The ith generator.}
   require 1 le i : "Invalid index";
   if Domain(H) eq Codomain(H) then i +:= 1; end if;
   require i le Rank(H) : "Invalid index";
   return H!([ 0 :k in [1..i-1] ] cat [1] cat [ 0 : k in [i+1..Rank(H)]]);
end intrinsic;

intrinsic '.'(H::HomCrvGrp,i::RngIntElt) -> MapCrvGrp
   {The ith generator.}
   require 1 le i : "Invalid index";
   if Domain(H) eq Codomain(H) then i +:= 1; end if;
   require i le Rank(H) : "Invalid index";
   return H!([ 0 :k in [1..i-1] ] cat [1] cat [ 0 : k in [i+1..Rank(H)]]);
end intrinsic;

function GeneratorLabels(H)
   if not assigned H`GeneratorLabels then
      if Domain(H) cmpeq Codomain(H) then
         H`GeneratorLabels := [ "" ] cat [ "$." * IntegerToString(k) : k in [1..Rank(H)-1] ];
      else
         H`GeneratorLabels := [ "$." * IntegerToString(k) : k in [1..Rank(H)] ];
      end if;
   end if;
   return H`GeneratorLabels;
end function;

intrinsic Print(f::MapCrvGrp, level::MonStgElt)
   {}
   if assigned f`Coordinates then
      C := f`Coordinates;
      if &and[ c eq 0 : c in C ]then
         printf "[0]";
      else
         X := GeneratorLabels(Parent(f));
         plus := "";
         for k in [1..#C] do
            if C[k] ne 0 then
               if C[k] lt 0 and plus ne "" then
                  C[k] *:= -1;
                  if plus eq "" then
  		     plus := "- ";
                  else
                     plus := " - ";
                  end if;
               end if;
               if X[k] eq "" or C[k] ne 1 then
                  printf "%o[%o]", plus, C[k];
                  if X[k] ne "" then
                     printf "*%o", X[k];
                  end if;
               else
                  printf "%o%o", plus, X[k];
               end if;
               plus := " + ";
            end if;
         end for;
      end if;
   end if;
   if level eq "Maximal" then
      S := DefiningMaps(f);
      C1 := Domain(f);
      A1 := AmbientSpace(C1);
      if IsAffine(A1) then sep := ", "; else sep := " : "; end if;
      P1 := CoordinateRing(A1);
      case Rank(P1) :
         when 1 : printf "(%o) :-> ", P1.1;
         when 2 : printf "(%o%o%o) :-> ", P1.1, sep, P1.2;
         when 3 : printf "(%o%o%o%o%o) :-> ", P1.1, sep, P1.2, sep, P1.3;
      end case;
      C2 := Codomain(f);
      A2 := AmbientSpace(C2);
      if IsAffine(A2) then sep := ", "; else sep := " : "; end if;
      case #S :
         when 1 : printf "(%o)", S[1];
         when 2 : printf "(%o%o%o)", S[1], sep, S[2];
         when 3 : printf "(%o%o%o%o%o)", S[1], sep, S[2], sep, S[3];
      end case;
   end if;
end intrinsic;

intrinsic 'eq'(H::HomCrvGrp,I::HomCrvGrp) -> BoolElt
   {}
   return Domain(H) cmpeq Domain(I) and Codomain(H) cmpeq Codomain(I);
end intrinsic;

intrinsic 'eq'(f::MapCrvGrp,g::MapCrvGrp) -> BoolElt
   {}
   return Parent(f) eq Parent(g) and f`Coordinates eq g`Coordinates;
end intrinsic;

intrinsic Parent(f::MapCrvGrp) -> HomCrvGrp
   {The parent of f.}
   return f`Parent;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Access Functions                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic DefiningMaps(f::MapCrvGrp) -> SeqEnum
   {}
   if not assigned f`RationalMaps then
      E := Domain(f);
      F := Codomain(f);
      if Category(E) eq CrvEll and E eq F then
         ;
      end if;
   end if;
   return f`RationalMaps;
end intrinsic;

intrinsic Domain(H::HomCrvGrp) -> Crv
   {The domain of f.}
   return H`Domain;
end intrinsic;

intrinsic Codomain(H::HomCrvGrp) -> Crv
   {The codomain of f.}
   return H`Codomain;
end intrinsic;

intrinsic Domain(f::MapCrvGrp) -> Crv
   {The domain of f.}
   return (f`Parent)`Domain;
end intrinsic;

intrinsic Codomain(f::MapCrvGrp) -> Crv
   {The codomain of f.}
   return (f`Parent)`Codomain;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Arithmetic and Functionality                    //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function BasisMorphism(M,k)
   if not assigned M`BasisMorphisms then
      E := Domain(M);
      if E eq Codomain(M) and Rank(M) eq 2 then
         K := BaseRing(E);
         error if Category(K) ne FldFin, "Basis morphisms unknown";
         q := #K;
         M`BasisMorphisms := [ hom< E -> E | P :-> P >,
  	    hom< E -> E | P :-> E![ a^q : a in Eltseq(P) ] > ];
      else
         error if true, "Basis morphisms not computed";
      end if;
   end if;
   return M`BasisMorphisms[k];
end function;

intrinsic Evaluate(f::MapCrvGrp,P::PtGrp) -> PtGrp
   {The image of P under f.}
   C := f`Coordinates;
   Q := Codomain(f)!0;
   for k in [1..#C] do
      if C[k] ne 0 then
         Q +:= C[k]*BasisMorphism(Parent(f),k)(P);
      end if;
   end for;
   return Q;
end intrinsic;

intrinsic IsIsomorphic(C::CrvGrp,D::CrvGrp) -> BoolElt, MapCrvGrp
   {Return true and the isomorphism if D is to C.}
   if C eq D then
      return true, Identity(End(C));
   end if;
   if IsAdditive(C) and IsAdditive(D) then
      return true;
   elif IsMultiplicative(C) and IsMultiplicative(D)
      and not (IsSplit(C) xor IsSplit(D)) then
      return true;
   end if;
   return false;
end intrinsic;

intrinsic Degree(f::MapCrvGrp) -> RngIntElt
   {}
   return Norm(f`Element);
end intrinsic;

intrinsic Trace(f::MapCrvGrp) -> RngIntElt
   {}
   return Trace(f`Element);
end intrinsic;

intrinsic Rank(H::HomCrvGrp) -> RngIntElt
   {}
   E := Domain(H);
   F := Codomain(H);
   require Category(E) eq CrvEll and Category(F) eq CrvEll :
      "Argument must be module of morphisms of elliptic curves.";
   K := BaseRing(E);
   if not assigned H`Rank then
      if Category(K) eq FldFin then
         t1 := TraceOfFrobenius(E);
         t2 := TraceOfFrobenius(F);
         if t1 ne t2 then
   	    H`Rank := 0;
         elif t1 mod Characteristic(K) ne 0 or t1^2 ne 4*#K then
   	    H`Rank := 2;
         else
  	    H`Rank := 4;
         end if;
      elif Category(K) eq FldRat then
         require false : "Not implemented";
      else
         require false :
            "Coeffficient ring of domain must " *
            "be a finite field or the rationals.";
      end if;
   end if;
   return H`Rank;
end intrinsic;

intrinsic Basis(H::HomCrvGrp) -> SeqEnum
   {}
   E := Domain(H);
   F := Codomain(H);
   require Category(E) eq CrvEll and Category(F) eq CrvEll :
      "Argument must be module of morphisms of elliptic curves.";
   K := BaseRing(E);
   return [ H!( [ 0 : k in [1..i-1] ] cat [1] cat
                [ 0 : k in [i+1..Rank(H)] ] ) : i in [1..Rank(H)] ];
end intrinsic;


