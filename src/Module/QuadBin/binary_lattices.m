////////////////////////////////////////////////////////////////////////
//                                                                    //
//                  LATTICES OF BINARY QUADRATIC FORMS                //
//                            David Kohel                             //
//                      Last modified April 2001                      //
//                                                                    //
////////////////////////////////////////////////////////////////////////

// Intrinsics: Lattice, ThetaSeries, RepresentationNumber

intrinsic Lattice(f::QuadBinElt) -> Lat
   {The Lattice of the binary quadratic form f.}
   D := Discriminant(f);
   require D lt 0 : "Discriminant of form must be negative";
   return LatticeWithGram(Matrix(2,[ f[1], f[2]/2, f[2]/2, f[3] ]));
end intrinsic;

intrinsic RepresentationNumber(f::QuadBinElt,n::RngIntElt : Primitive := false) -> RngIntElt
   {The nth representation number of the form f.}
   D := Discriminant(f);
   require D lt 0 : "Discriminant of argument 1 must be negative.";
   require n ge 0 : "Argument 2 must be nonnegative.";
   if n eq 0 then return 1; end if;
   m := GCD(Eltseq(f));
   if n mod m ne 0 then return IntegerRing()!0; end if;
   if IsPrime(n) and KroneckerSymbol(D,n) eq -1 then
       return 0;
   end if;
   f := ReducedForm(f);
   a, b, c := Explode(Eltseq(f));
   L := LatticeWithGram(Matrix(2,[ 2*a, b, b, 2*c ]));
   t := ThetaSeries(L,2*n);
   if Primitive then
       n1, n2 := SquareFreeFactorization(n);
       return IntegerRing()!&+[ MoebiusMu(n2 div m2)*Coefficient(t,2*(n1 * m2^2)) : m2 in Divisors(n2) ];
   else
       return IntegerRing()!Coefficient(t,2*n);
   end if;
end intrinsic;

intrinsic ThetaSeries(f::QuadBinElt,n::RngIntElt) -> RngSerElt
   {The theta series of the binary quadratic form f.}
   require Discriminant(f) lt 0 : "Discriminant of form must be negative";
   require n ge 0 : "Argument 2 must be nonnegative.";
   if n eq 0 then
       PS := PowerSeriesRing(IntegerRing());
       return PS!1 + O(PS.1);
   end if;
   a, b, c := Explode(Eltseq(ReducedForm(f)));
   L := LatticeWithGram(Matrix(2,[ 2*a, b, b, 2*c ]));
   t := ThetaSeries(L,2*n+1); S := Parent(t);
   return S![ Coefficient(t,2*k) : k in [0..n] ] + O(S.1^(n+1));
end intrinsic;

