intrinsic SquareFreeRoot(N::RngIntElt) -> RngIntElt
   {Returns the quotient by the largest square.}
   fact := Factorization(N);
   return Sign(N)*&*[ Integers() | 
      fact[i][1]^(fact[i][2] mod 2) : i in [1..#fact] ],
      &*[ Integers() | fact[i][1]^(fact[i][2] div 2) : i in [1..#fact] ];
end intrinsic;
