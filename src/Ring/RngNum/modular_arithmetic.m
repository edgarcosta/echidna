//////////////////////////////////////////////////////////////////// 
//                                                                //  
//          Residue Class Rings and Modular Unit Groups           // 
//                        by David Kohel                          // 
//                         January 2000                           // 
//                                                                // 
//////////////////////////////////////////////////////////////////// 

forward InverseModPrimePower, InverseModPrime;
forward UnitMapModPrime, UnitMapModPrime2, FlattenMultMap; 
forward AdditiveGroupModPrime, FlattenAddMap; 

// General GCD and CRT.

intrinsic Modorder(x::RngOrdElt,m::RngIntElt) -> RngIntElt
   {The order of x modulo m, or 0 if x is not a unit.}
   if GCD(Integers()!Norm(x),m) ne 1 then return 0; end if;
   ZZ := Integers();
   R := Parent(x);
   fact := Factorization(ideal< R | m >);
   prms := [ Factorization(ZZ!Norm(P[1]))[1,1] : P in fact ];
   t := LCM([ ZZ | Norm(P[1])-1 : P in fact ] cat
            [ ZZ | prms[i]^(fact[i][2]-1) : i in [1..#fact] ]);
   fact := Factorization(t);             
   for p in fact do
      i := 1; 
      while Modexp(x,t div p[1],m) eq 1 and i le p[2] do
         t div:= p[1];
         i +:= 1;
      end while;
   end for;
   return t;
end intrinsic;

intrinsic GCD(I::RngOrdIdl,J::RngOrdIdl) -> RngOrdIdl
   {}
   require IsIntegral(I) : "Argument 1 must be integral";
   require IsIntegral(J) : "Argument 2 must be integral";
   return I + J;
end intrinsic;

intrinsic CRT(X::[RngOrdElt],M::[RngOrdIdl]) -> RngOrdElt
   {The Chinese remainder lifting of the sequence of elements
   with respect to the sequence of moduli.}
   require #X eq #M : "Arguments must be of the same length";
   require #X ge 1 : "Arguments must be nonempty";
   require &and[ IsIntegral(I) : I in M ] : "Moduli must be integral";
   if #X eq 1 then
      return X[1];
   end if;
   x := X[1]; y := X[2];
   Remove(~X,1);
   I := M[1]; J := M[2];
   Remove(~M,1);   
   K := I+J; 
   require (x mod K) eq (y mod K) : 
      "Elements do not satisfy a common congruence";
   fact := Factorization(K);
   for p in fact do
      if Valuation(I,p[1]) eq p[2] then
         I *:= (p[1]^p[2])^-1;
      else
         J *:= (p[1]^p[2])^-1;
      end if;
   end for; 
   // Syntax should be: 
   // X[1] := CRT(x,y,I,J);
   X[1] := CRT(I,J,x,y);
   M[1] := I*J;
   return CRT(X,M);      
end intrinsic;

// Inverses.

/*
intrinsic InverseMod(a::RngOrdElt,m::RngIntElt) -> RngOrdElt
   {The inverse of a modulo m}
   R := Parent(a);
   require R eq ideal<R|a,m> : "Arguments must be coprime";
   return InverseMod(a,ideal<R|m>);
end intrinsic;

intrinsic InverseMod(a::RngOrdElt,I::RngOrdIdl) -> RngOrdElt
   {The inverse of a modulo I}
   R := Parent(a);
   require IsIntegral(I) : "Argument 2 must be integral";
   require R eq ideal<R|a,I> : "Arguments must be coprime";
   fact := Factorization(I);
   return CRT( [ InverseMod(a,p[1],p[2]) : p in fact ],
               [ p[1]^p[2] : p in fact ] );
end intrinsic;
*/

function InverseModPrimePower(a,P,r)
   Q := P^r;
   FF, proj := ResidueClassField(P);
   b := InverseModPrime(a,P);
   u := a*b mod Q;
   while u ne 1 do
      b1 := 1 - (b*a -1);
      b *:= b1 mod Q;
      u := a*b mod Q;
   end while;   
   return b;
end function;

function InverseModPrime(a,P)
   error if a in P, "Error: nonunit in InverseModPrime";
   FF, proj := ResidueClassField(P);
   return (proj(a)^-1)@@proj;
end function;

// Generic group flattening:

intrinsic EchelonForm(A::GrpAb) -> GrpAb, Map
   {The echelonized abelian group of A followed by the 
   isomorphism to A.}
   E, _, _, f := DirectSum(A,AbelianGroup([1]));
   return E, f;
end intrinsic;

// Syntax change:

/*
intrinsic ResidueClassField(P::RngOrdIdl) -> FldFin, Map
   {A finite field K followed by a homomorphism R -> K, 
   with kernel P.}
   require IsPrime(P) : "Argument 1 must be prime";
   return ResidueClassField(Order(P),P);
end intrinsic;
*/

// The uniformizing element of a prime ideal:

intrinsic UniformizingElement(P::RngOrdIdl) -> RngOrdElt
   {A uniformizing element for the prime P.}
   require IsPrime(P) : "Argument 1 must be prime";
   for x in Generators(P) do 
      if Valuation(x,P) eq 1 then
         return x;
      end if;
   end for;
   require false : 
      "Prime generators do not contain an element of valuation 1";
end intrinsic;

/*
intrinsic RingClassKernel(I::RngOrdIdl) -> GrpAb, Map
   {An abelian group A and a map A -> R, where R is the order 
   of I, inducing an isomorphism A -> ((R/I)^*)/(R^*(Z/mZ)^*), 
   where m is the characteristic of R/I.}
   R := Order(I);
   K, k := UnitGroup(R); 

end intrinsic;

intrinsic RayClassKernel(I::RngOrdIdl) -> GrpAb, Map
   {An abelian group A and a map A -> R, where R is the order 
   of I, inducing an isomorphism A -> ((R/I)^*)/R^*.}
   R := Order(I);
   K, k := UnitGroup(R); 

end intrinsic;
*/

intrinsic UnitGroupMod(I::RngOrdIdl) -> GrpAb, Map
   {An abelian group A and a map A -> R, where R is the 
   order of I, inducing an isomorphism A -> (R/I)^*.}
   R := Order(I);
   if IsPrime(I) then
      e := UnitMapModPrime(I,1);
      return Domain(e), e;
   end if;
   fact := Factorization(I);
   maps := [ UnitMapModPrime(p[1],p[2]) : p in fact ];
   if #maps eq 1 then
      return Domain(maps[1]), maps[1];
   end if;
   U := [ R | ]; 
   for k in [1..#fact] do
      Q := fact[k][1]^fact[k][2];
      e := maps[k];
      A := Domain(e); 
      J := I*(Q^-1);
      U cat:= [ CRT(Q,J,R!e(A.i),R!1) : i in [1..Ngens(A)] ];
   end for;
   C := AbelianGroup( &cat[ [ Order(C.i) : i in [1..Ngens(C)] ]
         where C is Domain(e) : e in maps ] );
   e := FlattenMultMap( map< C -> R | x :-> 
      &*[ R | U[i]^c[i] : i in [1..Ngens(C)] ] mod I 
         where c is Eltseq(x) >, R, I);  
   return Domain(e), e;
end intrinsic;

intrinsic AdditiveGroupMod(I::RngOrdIdl) -> GrpAb, Map
   {}
   R := Order(I);
   fact := Factorization(I); 
   maps := [ ];
   for p in fact do
      C, e := AdditiveGroupModPrime(p[1],p[2]); 
      Append(~maps,e);
   end for;
   if #fact eq 1 then
      return C, e;
   end if;
   X := [ R | ]; 
   for k in [1..#fact] do
      Q := fact[k][1]^fact[k][2];
      e := maps[k];
      A := Domain(e); 
      J := I*(Q^-1);
      X cat:= [ CRT([R|e(A.i),0],[Q,J]) : i in [1..Ngens(A)] ];
   end for;
   C := AbelianGroup( &cat[ [ Order(C.i) : i in [1..Ngens(C)] ]
         where C is Domain(e) : e in maps ] );
   e := FlattenAddMap( map< C -> R | x :-> 
      &+[ R | c[i]*X[i] : i in [1..Ngens(C)] ] mod I 
         where c is Eltseq(x) >, R, I);  
   return Domain(e), e;
end intrinsic;

function CyclotomicUnitMod(P,m,r)
   // Either 2 || m or Norm(P) is odd
   R := Order(P);
   K := FieldOfFractions(R);
   Q := P^r;
   fZ := CyclotomicPolynomial(m);
   f0 := PolynomialRing(R)!fZ;
   f1 := Derivative(f0);
   if R!2 in P and r ge 2 then
      assert false;
      z0 := R!-1;
   else 
      FF, proj := ResidueClassField(P);
      z0 := (Roots(PolynomialRing(FF)!fZ)[1][1])@@proj;   
   end if;
   c0 := Evaluate(f0,z0) mod Q;
   while c0 ne 0 do
      c1 := Evaluate(f1,z0) mod Q;
      z0 +:= -c0*InverseMod(c1,Q);
      c0 := Evaluate(f0,z0) mod Q;
   end while;
   return z0;
end function;

function CyclotomicGroupModPrime(P,r)
   // The cyclotomic units modulo the r-th power of a prime P.
   R := Order(P);
   m := Integers()!Norm(P)-1;   
   Q := P^r;
   if IsOdd(m) and R!2 notin Q then
      m *:= 2;
   end if;
   z := CyclotomicUnitMod(P,m,r); 
   U := AbelianGroup([m]);
   return U, map< U -> R | x :-> z^c[1] where c is Eltseq(x) >;   
end function;

function AdditiveGroupModPrime(P,r)
   // The additive group modulo the r-th power of a prime P.
   R := Order(P);
   q := Integers()!Norm(P);
   e := RamificationIndex(P); 
   f := InertiaDegree(P);
   _, p := IsPower(q,f);
   FF, proj := ResidueClassField(P);
   B := [ x@@proj : x in [ FF.1^i : i in [0..Degree(FF)-1] ] ];
   pi := UniformizingElement(P); 
   S := [ x*pi^i : x in B, i in [0..Min(e,r)-1] ]; 
   mods := [ p^Ceiling((r-Valuation(x,P))/e) : x in S ];
   A := AbelianGroup(mods);
   return A, map< A -> R | x :-> &+[ a[i]*S[i] 
      where a is Eltseq(x) : i in [1..#S] ] >;
end function;

function UnitMapModPrime(P,r)
   // The multiplicative group modulo the r-th power of a prime P.
   R := Order(P);
   if R!2 in P then
      return UnitMapModPrime2(P,r);
   end if;
   A0, f0 := CyclotomicGroupModPrime(P,r);
   if r eq 1 then
      return f0;
   else
      assert Ngens(A0) eq 1;
      u0 := f0(A0.1);
      A1, f1 := AdditiveGroupModPrime(P,1);
      Q := P^r;
      pi := UniformizingElement(P);
      U1 := [ u0 ] cat [ 1 + f1(A1.i)*pi mod Q : i in [1..Ngens(A1)] ];
      p := Order(A1.1);
      A := AbelianGroup([#A0] cat [ p^(r-1) : i in [1..Ngens(A1)] ]); 
      e := map< A -> R | x :-> &*[ U1[i]^c[i] mod Q 
         where c is Eltseq(x) : i in [1..Ngens(A)] ] >;
   end if; 
   return FlattenMultMap(e,R,Q);
end function;

function UnitMapModPrime2(P,r)
   // The multiplicative group modulo the r-th power of 
   // a prime P over (2).
   R := Order(P);
   Q := P^r;
   FF, proj := ResidueClassField(P);
   A, f := MultiplicativeGroup(FF);
   // Note that x@@f should be changed to f(x) once the 
   // return map is inverted:
   // 28/02/2000 -- Done.  
   // Elsewhere?
   if r eq 1 then
      return FlattenMultMap(map< A -> R | x :-> R!(f(x))@@proj >,R,P);
   end if;
   if R!2 notin Q then 
      r +:= -1;
      U1 := AbelianGroup([2]);
      u1 := map< U1 -> R | x :-> (-1)^c[1] where c is Eltseq(x) >;  
      A1, _, _, p0, p1 := DirectSum(A,U1);
      f1 := map< A1 -> R | x :-> u1(p1(x))*R!f(p0(x))@@proj >;
   else 
      A1 := A; 
      f1 := map< A -> R | x :-> R!f(x)@@proj >;
   end if;
   pi := UniformizingElement(P);
   A2, f2 := AdditiveGroupModPrime(P,r-1);
   A, _, _, p1, p2 := DirectSum(A1,A2);
   U1 := [ f1(A1.i) : i in [1..Ngens(A1)] ];
   U2 := [ 1 + R!f2(A2.j)*pi mod Q : j in [1..Ngens(A2)] ];
   e := map< A -> R | x :-> 
         &*[ R | U1[i]^a[i] mod Q : i in [1..Ngens(A1)] ] * 
         &*[ R | U2[j]^a[Ngens(A1)+j] mod Q : j in [1..Ngens(A2)] ] 
         mod Q where a is Eltseq(p1(x)) cat Eltseq(p2(x)) >;
   return FlattenMultMap(e,R,Q);
end function;

function FlattenMultMap(f,R,I)
   A := Domain(f);
   E, g := EchelonForm(A);  
   U := [ R | f(g(E.i)) : i in [1..Ngens(E)] ];
   return map< E -> R | x :-> 
      &*[ R | U[i]^c[i] mod I where c is Eltseq(x) 
         : i in [1..Ngens(E)] ] mod I >;
end function;

function FlattenAddMap(f,R,I)
   A := Domain(f);
   E, g := EchelonForm(A);  
   U := [ R | f(g(E.i)) : i in [1..Ngens(E)] ];
   return map< E -> R | x :-> 
      &+[ R | c[i]*U[i] where c is Eltseq(x) 
         : i in [1..Ngens(E)] ] mod I >;
end function;

