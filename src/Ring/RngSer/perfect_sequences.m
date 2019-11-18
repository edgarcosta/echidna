////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   Perfect Sequence Constructions                   //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic RandomPerfectSequence(FF::FldFin,N::RngIntElt) -> SeqEnum
   {}
   assert FF eq GF(2);
   S := [ One(FF) : i in [1..N] ];
   for i in [1..((N+1) div 2)] do
      S[2*i] := Random(FF);
      S[2*i+1] := S[2*i] + S[i];
   end for;
   return S;
end intrinsic;

intrinsic AlmostRandomPerfectSequence(FF::FldFin,m::RngIntElt,N::RngIntElt)
   -> SeqEnum 
   {}
   assert FF eq GF(2);
   S := [ One(FF) : i in [1..N] ];
   for i in [1..((N+1) div 2)] do
      if i lt m then
         S[2*i] := Random(FF);
      else
         S[2*i] := Zero(FF);
      end if;
      S[2*i+1] := S[2*i] + S[i];
   end for;
   return S;
end intrinsic;

intrinsic NullDimensions(A::SeqEnum,N::RngIntElt) -> AlgMatElt
   {}
   r := Min((N div 2) + 6,N);
   X := Zero(RMatrixSpace(Integers(),r,N));
   R := Universe(A);
   n := 1; k := 0;
   T := [* RMatrixSpace(R,k+1,n-k)![ R | A[1] ] *];
   for n in [2..N] do
      Append(~T,HorizontalJoin(T[n-1],
         RMatrixSpace(R,k+1,1)![ A[i] : i in [n-k..n] ]));
      X[k+1,n] := Dimension(NullSpace(T[n]));
   end for;
   for k in [1..r-1] do
      U := T;
      X[k+1,k] := k+1;
      for n in [k+1..N] do
         T[n] := VerticalJoin(U[n-1],
            RMatrixSpace(R,1,n-k)![ A[i] : i in [k+1..n] ]);
         X[k+1,n] := Dimension(NullSpace(T[n]));
      end for;
   end for;
   return X;
end intrinsic;

intrinsic NullBasis(A::SeqEnum,N::RngIntElt) -> AlgMatElt
   {}
   R := Universe(A);
   L := LinearComplexity(A,N);
   X := [* *];
   for n in [1..N] do
      k := L[n];
      M := RMatrixSpace(R,k+1,n-k)!
         &cat[ [ A[i+j-1] : j in [1..n-k] ] : i in [1..k+1] ];
      Append(~X,Basis(NullSpace(M)));
   end for;
   return X;
end intrinsic;

intrinsic LinearComplexity(A::SeqEnum,N::RngIntElt) -> SeqEnum
   {}
   X := NullDimensions(A,N);
   L := [ Zero(Integers()) : i in [1..N] ];
   L[1] := 1; k := 1;
   for n in [2..N] do
      while (X[k+1,n] le X[k,n-1]) do
         k +:= 1;
      end while;
      L[n] := k;
   end for;
   return L;
end intrinsic;

intrinsic LinearComplexity(A::SeqEnum) -> SeqEnum
   {}
   return LinearComplexity(A,#A);
end intrinsic;

intrinsic LinearComplexity(f::RngSerElt) -> SeqEnum
   {}
   N := RelativePrecision(f);
   PS := Parent(f);
   FF := BaseRing(PS);
   S0 := Eltseq(f);
   return LinearComplexity(S0 cat [ FF | Zero(PS) : i in [#S0+1..N] ]);
end intrinsic;

intrinsic LinearComplexity(f::RngSerElt,N::RngIntElt) -> SeqEnum
   {}
   PS := Parent(f);
   FF := BaseRing(PS);
   S0 := Eltseq(f + O((PS.1)^(N+1)));
   return LinearComplexity(S0);
end intrinsic;

intrinsic IsPerfect(S::SeqEnum) -> BoolElt
   {}
   LC := LinearComplexity(S);
   N := #LC;
   if LC[N] eq LC[N div 2] then 
      return false, 0; 
   end if;
   d := Max([ Max( 2*LC[i]-i, i-2*LC[i]-1 ) : i in [1..#LC] ]);
   return IsOne(d), d;
end intrinsic;

intrinsic IsPerfect(f::RngSerElt) -> BoolElt
   {}
   N := RelativePrecision(f);
   PS := Parent(f);
   FF := BaseRing(PS);
   S0 := Eltseq(f);
   return IsPerfect(S0 cat [ FF | Zero(PS) : i in [#S0+1..N] ]);
end intrinsic;

