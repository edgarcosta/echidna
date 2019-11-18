////////////////////////////////////////////////////////////////////
//                                                                //
//                   Ideals in Quadratic Orders                   //
//                        by David Kohel                          //
//                          June 2000                             //
//                                                                //
////////////////////////////////////////////////////////////////////

/*
I := <n,f> = <n,<a,b,c>>, where n is the content of the ideal. 
The norm of the ideal is then n^2*a, and the minimum -- a generator 
of the intersection with Z -- is n*a.
If J := <m,g> is another ideal, then I*J = <n*m*t,f*g> where t is 
f[1]*g[1] div (f*g)[1]. 
*/

forward FormTraceReduction;

declare type IdlQuad;

declare attributes IdlQuad : element;

/*
Nicole has done in C
*/
intrinsic Print(I::IdlQuad, level::MonStgElt)
   {}
   n, f := Explode(I`element);
   D := Discriminant(f);
   t := D mod 2;
   R := Order(I);
   m := Minimum(I);
   print "Ideal of", R;
   printf "Two element generators: %o, %o", 
       m, (n*(((D mod 2)-f[2]) div 2) mod m)+ n*R.1;
end intrinsic;

/*
Nicole has done in C using Order created from for R
*/
intrinsic Generators(I::IdlQuad) -> SeqEnum
   {}
   R := Order(I);
   D := Discriminant(R);
   n, f := Explode(I`element);
   m := Minimum(I);
   return [ R | [m,0], [(n*(((D mod 2)-f[2]) div 2) mod m),n] ];
end intrinsic;

/*
Nicole has done in C
*/
intrinsic HackQuadraticIdeal(f::QuadBinElt) -> IdlQuad
   {}
   I := New(IdlQuad);
   I`element := <1,FormTraceReduction(f)>;
   return I;
end intrinsic;

/* 
Nicole,

This should give the canonical form for hashing.

--David
*/
function FormTraceReduction(f)
   a,b,c := Explode(Eltseq(f));
   if Abs(b) lt Abs(a) or (a eq b and b gt 0) then
      return f; 
   end if;
   t := Floor(b/(2*a));
   return Parent(f)![a,b-2*t*a,c-t*b+a*t^2];
end function;

/*
Nicole has done in C - using ideal constructor with ring on
LHS and list or sequence on RHS
*/
intrinsic HackQuadraticIdeal(S::[RngQuadElt]) -> IdlQuad
   {}
   R := Universe(S);
   D := Discriminant(R);
   m := Conductor(R);	/* unused */
   DK := D div m^2;	/* unused */
   //
   // DRK-1 : I changed this matrix; this formulation is independent of 
   // any change in the generator R.1 -- we may want to allow this to be 
   // more general. 
   //
   // DRK-2: Use basis [R.1, 1] so that HermitForm eliminates the 
   // R.1 term from the second basis element, giving an ideal basis 
   // of the form [w,n].  
   //
   // Former matrix (of DRK-1): 
   //
   // M := Matrix(2,2,[0,1,-Norm(R.1),Trace(R.1)]);
   //
   // Matrix conjugated by [[0,1],[1,0]]:
   //
M := Matrix(2,2,[Trace(R.1),-Norm(R.1),1,0]);
// print "M:"; print M;
   A := HermiteForm( Matrix(
      &cat[ [ v, v*M ] where v is Vector(2,Eltseq(x)) : x in S ]) );
// print "Basis:"; print [ [A[2,2],A[2,1]], [A[1,2],A[1,1]] ];
   n := A[2,2];
   assert A[2,1] eq 0;
   w := R![A[1,2],A[1,1]];
// print "w =", w;
//
// End transposed block 
//
// print "Trace(w) =", Trace(w);
// print "Norm(w) =", Norm(w);
//
// Note the change of sign of Trace(w)!!!
//
   C := [ n, -Trace(w), Norm(w) div n ];
   // Compute the content as an ideal in R, not as a quadratic form! 
   cnt := GCD([A[1,1],A[1,2],n]); 
// print "cnt =", cnt; 
// print "C =", C; 
   I := New(IdlQuad);
   f := FormTraceReduction(QuadraticForms(D)![ x div cnt : x in C ]);
   I`element := <cnt,f>;
   // (Now correct for nonmaximal orders.)
   // This retains a nontrivial content in C when the ideal 
   // is noninvertible, and hence relies on the existence of 
   // forms <r*a,r*b,r*c> for r dividing the conductor.
   return I;
end intrinsic;

/* 
Nicole has done in C
*/
intrinsic Discriminant(I::IdlQuad) -> RngIntElt
   {}
   return Discriminant(I`element[2]);
end intrinsic;

/*
Nicole has done in C
*/
intrinsic Conductor(I::IdlQuad) -> RngIntElt
   {}
   D := Discriminant(I`element[2]);
   return Isqrt(D div FundamentalDiscriminant(D));
end intrinsic;

/*
Nicole has done in C
*/
intrinsic Reduction(I::IdlQuad) -> IdlQuad
   {}
   if Discriminant(I) gt 0 then
      R := ReductionOrbit(QuadraticForm(I));
      m := Abs(R[1][1]);
      for f in R do
         if Abs(f[1]) le m then 
   	    m := Abs(f[1]); 
            g := f; 
         end if;
      end for;
      return HackQuadraticIdeal(g); 
   end if; 
   return HackQuadraticIdeal(Reduction(QuadraticForm(I)));
end intrinsic;

/*
Nicole has done in C
*/
intrinsic 'eq'(I::IdlQuad,J::IdlQuad) -> BoolElt
   {}
   n1, f1 := Explode(I`element);
   n2, f2 := Explode(J`element);
   a := Abs(f1[1]);
   if n1 ne n2 then 
   print "n1 =", n1;  
   print n2;  
      return false;
   elif a ne Abs(f2[1]) then
      return false;
   end if;
   D := Discriminant(f1);    
   if D ne Discriminant(f2) then 
      return false;
   elif f1 eq f2 then
      return true;
   end if;
   return f1[2] mod (2*a) eq f2[2] mod (2*a);
end intrinsic;

/*
Nicole has done in C
*/
intrinsic Norm(I::IdlQuad) -> RngIntElt
   {}
   return Abs(I`element[1]^2*I`element[2][1]);
end intrinsic;

/*
Nicole has done in C
*/
intrinsic Minimum(I::IdlQuad) -> RngIntElt
   {}
   return Abs(I`element[1]*I`element[2][1]);
end intrinsic;

/*
Nicole has done in C
*/
intrinsic Order(I::IdlQuad) -> RngIntElt
   {}
   return sub< MaximalOrder(
      QuadraticField(Discriminant(I))) | Conductor(I) >;
end intrinsic;

/*
Nicole has done in C
*/
intrinsic Conjugate(I::IdlQuad) -> IdlQuad
   {}
   J := New(IdlQuad);
   J`element := <Content(I),-QuadraticForm(I)>;
   return J;
end intrinsic;

/*
Nicole has done in C
*/
intrinsic Content(I::IdlQuad) -> RngIntElt
   {}
   return I`element[1];
end intrinsic;

/*
Nicole has done in C
*/
intrinsic QuadraticForm(I::IdlQuad) -> QuadBinElt
   {}
   return I`element[2];
end intrinsic;

/*
Nicole has done in C
*/
intrinsic '*'(I::IdlQuad,J::IdlQuad) -> IdlQuad
   {}
   n, f := Explode(I`element);
   m, g := Explode(J`element);
   h := Composition(f,g : NoReduction);
   P := New(IdlQuad);
   P`element := <n*m*(f[1]*g[1] div h[1]),h>;
   return P;
end intrinsic;

/*
Nicole has done in C
*/
intrinsic '^'(I::IdlQuad,r::RngIntElt) -> IdlQuad
   {}
   n, f := Explode(I`element);
   g := f;
   for i in [1..r-1] do
      g := Composition(f,g : NoReduction);
   end for;
   J := New(IdlQuad);
   J`element := <n^r*(f[1]^r div g[1]),g>;
   return J;
end intrinsic;


