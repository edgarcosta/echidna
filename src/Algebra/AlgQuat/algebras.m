//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                            QUATERNION ALGEBRAS                           //
//  Copyright (C) 2002 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          Creation Functions                              //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function Discriminants(N,M,B)
   // PRE: N is a product of ODD prime powers, and M is 
   // relatively prime to N.
   // POST: Determines a list of discriminants in which all 
   // prime factors of N are inert, and all prime factors of 
   // M are split, up to a bound in N*M.

   B0 := Isqrt(4*N*M);
   error if GCD(N,M) ne 1,
      "Common prime in split and ramifying lists.";
   RamifyingFactors := Factorization(N);
   SplitFactors := Factorization(M);
   ReturnDiscs := [ -4*n+j : j in [1,0] , n in [Max(1,B0-B)..B0+B] ];
   for D in ReturnDiscs do
      for q in RamifyingFactors do 
         if KroneckerSymbol(D,q[1]) ne -1 then
            Exclude(~ReturnDiscs,D);
         end if;
      end for;
      for p in SplitFactors do 
         if KroneckerSymbol(D,p[1]) ne 1 then
            Exclude(~ReturnDiscs,D);
         end if;
      end for;
   end for;
   return ReturnDiscs;
end function;

function TraceValues(D1,D2,N,M)
   // PRE: All factors of N inert and all factors of M split 
   // in D1 and D2.
   // POST: For an integer T set D = (D1*D2 - T^2).  Returns 
   // the T for which D is positive, D mod 4*N*M is zero, 
   // Q = D div 4*N*M is relatively prime to N, and all 
   // factors of Q are either split in one of D1 or D2 or 
   // inert in D1 or D2 and divide Q to an even power.

   // Stupid, but here goes...
   Tmax := Isqrt(D1*D2 div 4);
   T := -Tmax;
   prms := PrimeDivisors(N) cat PrimeDivisors(M);
   rts := [ Integers() | ];
   Tvals := [ (D1 mod 2)*(D2 mod 2) ];
   m := 2; 
   if 2 in prms then
      Exclude(~prms,2);
      m := 8; 
      D := ((D1 mod 4)*(D2 mod 4)) mod 8;
      if D in { 0, 1 } then
         Tvals := [ D, D + 4 ];
      elif D eq 4 then
         Tvals := [ 2, 6 ];
      end if;
   end if;
   for p in prms do
      t := PolynomialRing(FiniteField(p)).1;
      a := Roots(t^2 - D1*D2)[1][1];
      Append(~rts,Integers()!a);
   end for;
   for i in [1..#prms] do 
      p := prms[i]; 
      a := rts[i];
      Tvals := &join[ { x : x in &join[ { y, p*m - y } : 
         y in [ CRT([a0,a1],[p,m]) : a0 in [-a,a] ] ]
         | Abs(x) le Tmax } : a1 in Tvals ];
      m *:= p;
   end for;
   for T in Tvals do
      Q := (D1*D2 - T^2) div (4*N*M);
      if Q eq 1 then 
         return [ T ];
      elif GCD(Q,N) ne 1 then
         Exclude(~Tvals,T);
      else
         OtherFactors := Factorization(Q);
         for p in OtherFactors do
            if KroneckerSymbol(D1,p[1]) ne 1 or 
               KroneckerSymbol(D2,p[1]) ne 1 then
               Exclude(~Tvals,T);
            end if;
         end for;
      end if;
   end for;
return [ T : T in Tvals ];
end function;

/*
intrinsic QuaternionAlgebra(N::RngIntElt) -> AlgQuat
   {Returns a rational quaternion algebra of discriminant N.}

   fact := Factorization(N);
   require (#fact mod 2) eq 1 :
      "This constructor exists only for definite quaternions.";
   require N gt 0 and &and [ p[2] eq 1 : p in fact ] : 
      "Discriminant must be a square-free positive integer.";  
   // First test for the easy cases.
   if N eq 2 then 
      return QuaternionAlgebra(-3,-3,1);
   elif (N mod 4) eq 3 and 
     &and [ KroneckerSymbol(-4,p[1]) eq -1 : p in fact ] then
     return QuaternionAlgebra(-4,-N,0);
   elif (N mod 8) eq 5 and 
     &and [ KroneckerSymbol(-8,p[1]) eq -1 : p in fact ] then
     return QuaternionAlgebra(-8,-((N+1) div 2),2);
   end if;
   B := Ceiling(Log(N));
   for k in [1..8] do
      DiscList := Discriminants(N,1,2^k*B);
      DiscPairs := [ [D1,D2] : D2, D1 in DiscList | D1*D2 gt (4*N) ];
      for D in DiscPairs do
         TList := TraceValues(D[1],D[2],N,1); 
         if #TList gt 0 then 
            A := QuaternionAlgebra(D[1],D[2],TList[1]);
            if Discriminant(A) eq N then
               return A;
            end if;
         end if;
      end for;
   end for;             
   return "Error, no order found (please report).";
end intrinsic;
*/

function RandomElement(A,S)
   return A![ Random(S) : i in [1..4] ];
end function;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         Units and Unit Groups                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Units(S::AlgQuatOrd) -> SeqEnum
   {The units in the quaternion order S over the integers.}
   K := QuaternionAlgebra(S);
   require Type(BaseRing(S)) eq RngInt :
      "Base ring of argument must be the integers."; 
   require IsDefinite(K) : "Quaternion algebra must be definite.";
   if K!1 notin S then return [ S | ]; end if;
   X := ShortestVectors(LatticeWithGram(GramMatrix(S)));
   U := [ u * S!Eltseq(v) : u in [1,-1], v in X ];   
   ords := [ #{ u^j : j in [0..5] } : u in U ];
   if #U le 6 then // cyclic group
       i := Index(ords,#U);
       U := [ (-1)^t*U[i]^j : t in [0,1], j in [0..(#U div 2) -1] ];
   elif #U eq 8 then
       C4 := {@ {U[i],-U[i]} : i in [1..8] | ords[i] eq 4 @};
       U := [S!1,S!-1] cat &cat[ [u,-u] where u := Rep(c) : c in C4 ];
   elif #U eq 12 then
       i := Index(ords,4); j := Index(ords,3);
       U := [ (-1)^t*U[i]^n*U[j]^m : t, n in [0..1], m in [0..2] ];
   elif #U eq 24 then
       i := Index(ords,3);
       C4 := {@ {U[i],-U[i]} : i in [1..24] | ords[i] eq 4 @};
       U4 := [S!1,S!-1] cat &cat[ [u,-u] where u := Rep(c) : c in C4 ];
       U := [ u*U[i]^j : u in U4, j in [0..2] ];
   end if;
   return U;
end intrinsic;

function RightRegularRepresentation(U,X)
    G := Sym(#U);
    gens := [ G![ Index(U,x*u) : x in U ] : u in U ];
    if #X eq 1 then
        H := sub< G | gens >;
    else
        subgens := [ G![ Index(U,x*u) : x in U ] : u in X ];
        H := sub< G | gens >;
        K := sub< G | subgens >;
        m := RegularRepresentation(H,K);
        gens := [ m(g) : g in H ];
        H := Codomain(m);
    end if;
    iso := [ <gens[i],U[i]> : i in [1..#U] ];
    return H, map< H -> U | iso >;
end function;

intrinsic UnitGroup(S::AlgQuatOrd) -> GrpPerm, Map
    {}
   A := QuaternionAlgebra(S);
   require Type(BaseRing(S)) eq RngInt :
      "Base ring of argument must be the integers."; 
   require IsDefinite(A) : "Quaternion algebra must be definite.";
   require A!1 in S : "Argument must be a quaternion order.";
   U := Units(S);
   if #U ne 24 then
       X := [ U[1] ];
   else
       X := [ U[1], U[9], U[17] ];
   end if;
   return RightRegularRepresentation(Units(S),X);
end intrinsic;
