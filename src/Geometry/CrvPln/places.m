////////////////////////////////////////////////////////////////////////
//                                                                    //
//                 Places on Projective Plane Curves                  //
//                           David R. Kohel                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////

intrinsic ResidueClassField(P::PlcCrvElt) -> Rng
   {}
   return ResidueClassField(FunctionFieldPlace(P));
end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Place(C::Crv,Z::Sch) -> Rng
   {}
   require Ambient(Z) eq Ambient(C) and Z subset C : 
       "Argument 2 must be a subscheme of argument 1.";
   require Dimension(Z) eq 0 and IsIrreducible(Z) : 
       "Argument 2 must be a dimension 0 prime subscheme.";
   return Support(Divisor(DivisorGroup(C),Z))[1];
end intrinsic;

