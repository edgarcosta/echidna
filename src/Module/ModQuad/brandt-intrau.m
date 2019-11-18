////////////////////////////////////////////////////////////////////////
//                                                                    //
//                   BRANDT-INTRAU LATTICE CONSTRUCTOR                //
//                                                                    //
////////////////////////////////////////////////////////////////////////


intrinsic BrandtIntrauLattice(S::[RngIntElt]) -> Lat
   {The even lattice with associated quadratic form 
       a*x^2 + b*y^2 + c*z^2 + d*y*z + e*x*z + f*x*y,
   where S = [a,b,c,d,e,f].}
   require #S eq 6 : "Invalid sequence length";
   require Type(Universe(S)) eq RngInt : "Invalid sequence universe";
   a, b, c, d, e, f := Explode(S);
   return LatticeWithGram( MatrixAlgebra(Integers(),3) !
         [ 2*a,f,e, f,2*b,d, e,d,2*c ] ); 
end intrinsic;

