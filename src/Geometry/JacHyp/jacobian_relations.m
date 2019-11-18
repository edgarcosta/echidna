//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Group Relations in the Jacobian of a Hyperelliptic Curve                //  
//  Copyright (C) 2000 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare verbose JacobianGroup, 2;

function RandomVector(V,t)
   return V ! [ Random([-t..t]) : j in [1..Degree(V)] ];
end function;

function RandomPolynomial(FF,d)
   return PolynomialRing(FF)![ Random(FF) : k in [0..d] ];
end function;

function SmoothPrime(J,d)
   FF := BaseRing(J);
   h, f := DefiningPolynomials(Curve(J));
   while true do
      p := RandomPolynomial(FF,d);
      if Degree(p) ge 1 and IsIrreducible(p) then
         if Degree(p) eq 1 then
            PK := PolynomialRing(FF); T := PK.1;
            rts := Roots(T^2+(h mod p)*T-(f mod p));
            if #rts gt 0 then
               return J![p,rts[1][1]];
            end if;
         elif Degree(p) gt 2 then
            K<x> := ext< FF | p >;
            PK := PolynomialRing(K); T := PK.1;
            rts := Roots(T^2+Evaluate(h,x)*T-Evaluate(f,x));
            if #rts gt 0 then
    	       b := PolynomialRing(FF)!Eltseq(rts[1][1]);
               return J![p,b];
            end if;
         end if;
      end if;
print "Failed";
   end while;
end function;

function SmoothReduction(Q,gens)
   V := RSpace(Integers(),#gens);
   u := V!0;
   if Q eq Parent(Q)!0 then return Q, u; end if;
   // print "Initial Q:", Q;
   if GetVerbose("JacobianGroup") ge 2 then
      factor_base := [ p[1] : p in Factorization(Q[1]) ];
      degs := [ Degree(p) : p in factor_base ]; 
      // print "Point is sum of places with degrees:";
      // print degs;
      // Try returning early if factorization shows non-smooth element:
      if Max(degs) gt Degree(gens[#gens][1]) then
         return Q, u;
      end if; 
   end if;
   for k in [1..#gens] do 
      P := gens[k];
      while Q[1] mod P[1] eq 0 do
         Q1 := Q + P;
         if Q[1] mod Q1[1] eq 0 then 
            Q := Q1;
            u[k] -:= 1;
         else 
   	    Q -:= P;
            u[k] +:= 1;
         end if;
      end while;
   end for;
   return Q, u;
end function;

function SmoothnessBase(J,n)
   F := BaseRing(J);
   g := Dimension(J);
   q := #F;
   h, f := DefiningPolynomials(Curve(J));
   t := Ceiling(Log(n)/Log(q));
   // This should have be handled elsewhere:
   assert t lt g;
   PF := PolynomialRing(F); X := PF.1;
   gens := [ J | ];
   for a in F do 
      rts := Roots(X^2+Evaluate(h,a)*X-Evaluate(f,a));
      if #rts gt 0 then 
         Q := J![X-a,rts[1][1]]; 
         Append(~gens,Q);
         if #gens eq n then return gens; end if;
      end if;
   end for;
   vprintf JacobianGroup: "Constructing generator list of size %o\n", n;
   r := 1;
   while true do
      vprintf JacobianGroup: "Found #gens = %o\n", #gens;
      r +:= 1;
      K := ext< F | IrreduciblePolynomial(F,r) >;
      prms := { PF | };
      for a in K do
         p := MinimalPolynomial(a);
         if Degree(p) eq r and p notin prms then
  	    L := ext< F | p >;
            rts := Roots(Y^2+(L!h)*Y-L!(f)) 
                      where Y is PolynomialRing(L).1;
            if #rts gt 0 then
               Q := J![p,PF!Eltseq(rts[1][1])];
               Append(~gens,Q);
               Include(~prms,Q[1]);
            end if; 
            if #gens eq n then 
               vprintf JacobianGroup: "Found #gens = %o\n", n;
               return gens; 
            end if;
         end if;
      end for; 
   end while;
end function;

intrinsic AbelianGroupStructure(J::JacHyp : 
      Scalar := 1, NumberOfGenerators := 0) -> Map, Map
   {Returns two maps, one from a free abelian group F to the group of 
   rational points on J, and a second map f from F an abstract abelian 
   group A isomorphic to the group of points of J.}

   require IsOdd(Degree(Curve(J))) : "Curve must be an odd degree model";
   g := Dimension(J);
   FF := BaseRing(J);   
   q := #FF;
   s := Exp((1/2)*(g*Log(q))^(1/2)*Log(g*Log(q))^(1-1/2));
   s := Ceiling(Scalar*s);
   if NumberOfGenerators eq 0 then
      r := Max(8,Ceiling(Sqrt(s)));
   else 
      require NumberOfGenerators gt 0 : 
         "Parameter NumberOfGenerators must be positive.";
      r := NumberOfGenerators;
   end if;
   vprint JacobianGroup : "Number of generators =", r; 
   vprint JacobianGroup : "Smoothness base size =", s; 
   rels, gens := JacobianRelations(J,r : ExtraGenerators := Max(0,s-r));
   F := FreeAbelianGroup(r);
   A, m := quo< F | [ F | Eltseq(rels[i]) : i in [1..r] ] >;
   h := hom< F -> J | x :-> 
      &+[ c[i]*gens[i] : i in [1..r] ] where c is Eltseq(x) >;
   return h, m;
end intrinsic;

intrinsic JacobianRelations(J::JacHyp,r::RngIntElt : 
   ExtraGenerators := 0) -> ModTupRng {}
   require Category(ExtraGenerators) eq RngIntElt and ExtraGenerators ge 0 : 
      "Parameter 'ExtraGenerators' must be a non-negative integer.";
   require IsOdd(Degree(Curve(J))) : "Curve must be an odd degree model";
   FF := BaseRing(J);
   require Type(FF) eq FldFin : "Curve must be defined over a finite field.";
   require Dimension(J) ge 2 : "Jacobian must be of dimension at least 2";
   q := #FF;
   g := Dimension(J);
   e := ExtraGenerators;
   // N := #J; // No good algorithm for group order.
   sbase := SmoothnessBase(J,r+e);
   gens := sbase[1..r];
   vprint JacobianGroup : "Using generators of degree up to", Degree(sbase[#sbase][1]);
   V0 := RSpace(Integers(),r);
   V1 := RSpace(Integers(),r+e);
   t := 0;
   B0 := Max(6,g div (r+e));
   // Should estimate the probability of finding a relation,
   // or use a different exit strategy:
   B1 := Max([2*(r+e),Ceiling(8*g*Log(q)),32]);
   S := [ V1 | ];
   if GetVerbose("JacobianGroup") ge 2 then
      printf "Using random coefficient bound = %o\n", B0;
      printf "Using cycles each of %o trials\n", B1;
   end if;
   N0 := 2^Ceiling(g*Log(2,r+e));
   if t mod 8 eq 0 and GetVerbose("JacobianGroup") ge 1 then
      print "Building relation matrix.";
   end if;
   rnk := 0;
   while true do
      t +:= 1;
      for k in [1..B1] do
         v0 := RandomVector(V0,B0);
         Q := &+[ v0[i]*sbase[i] : i in [1..r] ];
         R, u := SmoothReduction(Q,sbase); 
         if R eq J!0 then
            r1 := Vector( Eltseq(v0) cat [ 0 : i in [r+1..r+e] ] ) - 
                  Vector( Eltseq(u)[1..r] 
                          cat [ N0*u[i] : i in [r+1..r+e] ] );
            if r1 ne 0 then 
               Append(~S,r1); 
            end if;
         end if;
      end for;
      // Matrix needs non-empty sequence
      deg := #sbase;
      tot_rels := #S;
      vprintf JacobianGroup : "Found %o relations out of %o\n", 
         tot_rels - rnk, B1;
      if #S gt 0 then
         prev_rnk := rnk; // Only needed for verbosity.
         M := LLL( Matrix(S) ); 
         rnk := Rank(M);
         M := Matrix([ M[k] : k in [1..rnk] ]);
         S := [ M[i] : i in [1..rnk] ];
         if GetVerbose("JacobianGroup") ge 1 then
            printf "Relation matrix rank = %o/%o\n", rnk, deg;
            new_rnk := rnk - prev_rnk;
            old_rnk := tot_rels - #S;
            vprint JacobianGroup, 2 : "   old:", old_rnk;
            vprint JacobianGroup, 2 : "   new:", new_rnk;
         end if;
         if rnk ge r then 
            if &and[ M[i,j] eq 0 : i in [1..r], j in [r+1..r+e] ] then
	       M0 := Matrix(r,r,[ M[i,j] : i, j in [1..r] ]);
               if Abs(Determinant(M0)) lt (1+Sqrt(q))^(2*g) then
     	          return M0, sbase[1..r];
               end if;
            end if;      
         end if;      
      end if;
      if t mod 8 eq 0 and GetVerbose("JacobianGroup") ge 1 then
         printf "<...completed %o iterations>\n", t;
      end if;
   end while;
end intrinsic;









