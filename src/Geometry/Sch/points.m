////////////////////////////////////////////////////////////////////
//                                                                //
//               Points on Projective Plane Curves                //
//                                                                //
////////////////////////////////////////////////////////////////////

/*
See various functions for primary decomposition and the like --
in particular 
*/

intrinsic PointEnumeration(X::Sch : Bound := 0) -> SetIndx
    {}
    K := BaseRing(X);
    if Dimension(X) eq 0 and IsField(K) then
	_, X := IsCluster(X);
	return Support(X);
    elif Type(K) eq FldFin then
	return Points(X);
    elif Type(X) eq CrvHyp then
	if Type(K) eq FldRat then
	    require Bound gt 0 :
	       "A positive height bound must be specified.";
	    h := DefiningPolynomials(X);
	    require h eq 0 : "Curve must be in the form y^2 = f(x).";
	    return Points(X : Bound := Bound); 
	end if;
    elif Type(X) eq CrvEll then
	if Type(K) eq FldRat then
	    require Bound gt 0 :
	       "A positive height bound must be specified.";
	    C, m := HyperellipticCurve(X);
	    _, inv := EllipticCurve(C);
	    h := DefiningPolynomials(C);
	    require h eq 0 : "Curve must be in the form y^2 = f(x).";
	    // Temporary workaround -- map returns a function from
	    // rings to pointset maps.
	    return {@ X | P@(inv(BaseRing(C))) :
	                     P in Points(C : Bound := Bound) @};
	end if;
    end if;
    require false : "Point enumeration not defined for this scheme.";
end intrinsic;

intrinsic GaloisConjugates(P::Pt) -> SetEnum
   {}
   L := Ring(Parent(P));
   K := BaseRing(Scheme(P));
   require Type(K) eq FldFin : 
      "The parent scheme of the argument must be a finite field.";
   require Type(L) eq FldFin : 
      "The coefficient ring of the argument must be a finite field.";
   q := #K;  
   _, r := IsPowerOf(#L,q);
   S := Eltseq(P);
   return { Parent(P)![ x^q^i : x in S ] : i in [0..r-1] };
end intrinsic;

intrinsic IsConjugate(P::Pt,Q::Pt) -> BoolElt
   {Return true if and only if P is a Galois conjugate of Q, 
   the coefficient rings of P and Q is a finite field.}

   require Parent(P) eq Parent(Q) : 
     "Arguments must be points in the same pointset.";
   L := Ring(Parent(P));
   require Type(L) eq FldFin :
      "Arguments must be defined over a finite field";
   return P in GaloisConjugates(Q);
end intrinsic;







