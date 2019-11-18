////////////////////////////////////////////////////////////////////
//                                                                //
//                 CLASS GROUPS OF QUADRATIC ORDERS               //
//                          David Kohel                           //
//                         Created Today                          //
//                                                                //
////////////////////////////////////////////////////////////////////

// intrinsics: ClassGroup

/*
intrinsic ClassGroup(R::RngQuad) -> GrpAb, Map
   {My test class group.}
   G, f := ClassGroup(BinaryQuadraticForms(Discriminant(R)));
   I := ideal< R | 1 >;
   return G, func< x | QuadraticIdeal(f(x)) >;
       // hom< G -> Parent(I) | x :-> QuadraticIdeal(f(x)) >;
end intrinsic;
*/
