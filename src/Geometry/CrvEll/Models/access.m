//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//         Copyright (C) 2011 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic IsEllipticCurve(E::Crv) -> BoolElt
    {Returns true if E is an elliptic curve model with fixed base point
    and addition law structure.}
    if Type(E) eq CrvEll then return true; end if;
    /* If any of EllipticModelType, WeierstrassMorphism, or IdentityElement
    have been assigned, then we presume that the curve has genus 1. */
    if assigned E`EllipticModelType then
        // This assumes some minimal associated data is assigned
        assert assigned E`IdentityElement;
        return true;
    elif assigned E`WeierstrassMorphism then
        // All data can be pulled back from this isomorphism.
        return true;
    elif assigned E`IdentityElement then
        // A Weierstrass morphism can be constructed from this data.
        return true;
    end if;
    return false;
end intrinsic;

intrinsic AdditionMorphism(C::Crv) -> MapSch
    {}
    if not assigned C`AdditionMorphism then
	if not assigned C`WeierstrassMorphism then
            require assigned C`IdentityElement :
		"Argument must be an elliptic curve model.";
	    E, i := EllipticCurve(C,C`IdentityElement);
	    C`WeierstrassMorphism := i;
	end if;
        i := C`WeierstrassMorphism;
        E := Codomain(i);
        bool, j := IsInvertible(i); assert bool;
	mu := AdditionMorphism(E);
	ExE := Domain(mu);
	CxC := ProductScheme(C,2);
	PxP := AmbientSpace(CxC);
	n := Length(AmbientSpace(C));
	XX := [ PxP.i : i in [1..n] ];
	YY := [ PxP.i : i in [n+1..2*n] ];
	polys := AllDefiningPolynomials(i);
	ixi := map< CxC->ExE |
	    [ [ f(XX) : f in S1 ] cat [ f(YY) : f in S2 ] : S1, S2 in polys ] >;
	C`AdditionMorphism := ixi * mu * j;
    end if;
    return C`AdditionMorphism;
end intrinsic;

intrinsic EllipticModelType(C::Crv) -> MonStgElt
    {}
    require assigned C`EllipticModelType :
	"Argument must be an elliptic curve model.";
    return C`EllipticModelType;
end intrinsic;

intrinsic EllipticModelInvariants(C::Crv) -> MonStgElt
    {}
    require assigned C`EllipticModelInvariants :
	"Argument must be an elliptic curve model.";
    return C`EllipticModelInvariants;
end intrinsic;

intrinsic EmbeddingClass(C::Crv) -> Pt
    {The point S on the (elliptic) curve C with degree
    d embedding, such that the embedding divisor is
    (d-1)(O) + (S); in particular, C is a symmetric
    embedding if and only if S is in C[2].}
    if Type(C) eq CrvEll then return C!0; end if;
    require assigned C`EmbeddingClass :
	"Argument must be an elliptic curve model with embedding class assigned.";
    return C!C`EmbeddingClass;
end intrinsic;

intrinsic Identity(C::CrvEll) -> Pt
    {}
    return C!0;
end intrinsic;

intrinsic Identity(C::Crv) -> Pt
    {The identity element on the elliptic curve C.}
    if Type(C) eq CrvEll then return C!0; end if;
    require assigned C`IdentityElement: "Identity element not assigned for the curve.";
    return C!C`IdentityElement;
end intrinsic;

intrinsic '!'(C::Crv,zero::RngIntElt) -> Pt
    {The identity element on the elliptic curve C.}
    require zero eq 0: "Argument 2 must be zero.";
    if Type(C) eq CrvEll then return C!0; end if;
    require assigned C`IdentityElement: "Identity element not assigned for the curve.";
    return C!C`IdentityElement;
end intrinsic;

intrinsic IdentityMorphism(C::Crv) -> MapSch
    {}
    A := CoordinateRing(AmbientSpace(C));
    B := [A.i : i in [1..Ngens(A)]];
    return map< C->C | B, B >;
end intrinsic;

intrinsic InverseMorphism(C::Crv) -> MapSch
    {}
    require assigned C`InverseMorphism :
	"Argument must be an elliptic curve model.";
    return C`InverseMorphism;
end intrinsic;

intrinsic DoublingMorphism(C::Crv) -> MapSch
    {}
    A := CoordinateRing(AmbientSpace(C));
    B := [A.i : i in [1..Ngens(A)]];
    require IsEllipticCurve(C) :
        "Argument must be an elliptic curve model.";
    if not assigned C`DoublingMorphism then
        require assigned C`AdditionMorphism :
            "Argument must be an elliptic curve model with prescribed structure.";
        mu := AdditionMorphism(C);
        II := DefiningIdeal(C);
        B2 := { NormalForm([ f(B cat B) : f in S ],II) : S in Eltseq(mu) };
        B2 := { S : S in B2 | 0 notin S };
        B2 := { [ f div g : f in S ] where g := GCD(S) : S in B2 };
        C`DoublingMorphism := map< C->C | [ S : S in B2 ] >;
    end if;
    return C`DoublingMorphism;
end intrinsic;

intrinsic MontgomeryBasePoint(C::Crv) -> MapSch
    {}
    require assigned C`MontgomeryMorphism :
	"Argument must be an Kummer-oriented product elliptic curve.";
    return C!C`MontgomeryBasePoint;
end intrinsic;

intrinsic MontgomeryMorphism(C::Crv) -> MapSch
    {}
    require assigned C`MontgomeryMorphism :
	"Argument must be an Kummer-oriented product elliptic curve.";
    return C`MontgomeryMorphism;
end intrinsic;

intrinsic MontgomeryMultiplication(P::Pt,n::RngIntElt) -> MapSch
    {}
    E := Scheme(P);
    require ISA(Type(E),Crv) : "Argument 1 must be a point on a curve.";
    require IsEllipticCurve(E) : "Argument 1 must be a point on an elliptic curve.";
    K, phi := EllipticCurve_MontgomeryOriented_KummerProduct(E,P);
    if n lt 0 then
        return MontgomeryMultiplication(-P,-n);
    elif n eq 0 then
        return phi(E!0);
    elif n eq 1 then
        return phi(P);
    end if;
    m1 := K`MontgomeryMorphism;
    s2 := K`MontgomeryInversion;
    m2 := s2*m1*s2;
    bb := Reverse(IntegerToSequence(n-1,2));
    Q := phi(P);
    for bi in bb do
        if bi eq 0 then
            Q := m2(Q);
        else
            Q := m1(Q);
        end if;
    end for;
    return Q;
end intrinsic;

intrinsic KummerCurve(C::CrvEll) -> MapSch
    {}
    pi := KummerMorphism(C);
    return Codomain(pi), pi;
end intrinsic;

intrinsic KummerCurve(C::Crv) -> MapSch
    {}
    require IsEllipticCurve(C) :
	"Argument must be an elliptic curve model.";
    require assigned C`KummerMorphism :
	"Argument must be an elliptic curve model with prescribed structure.";
    pi := C`KummerMorphism;
    return Codomain(pi), pi;
end intrinsic;

intrinsic KummerMorphism(C::CrvEll) -> MapSch
    {}
    if not assigned C`KummerMorphism then
        K := BaseRing(C);
        P2<X,Y,Z> := AmbientSpace(C);
        P1<U,V> := Curve(ProjectiveSpace(K,1));
        C`KummerMorphism := map< C->P1 | [X,Z] >;
    end if;
    return C`KummerMorphism;
end intrinsic;

intrinsic KummerMorphism(C::Crv) -> MapSch
    {}
    require IsEllipticCurve(C) :
	"Argument must be an elliptic curve model.";
    if not assigned C`KummerMorphism then
        E, phi := WeierstrassModel(C);
        C`KummerMorphism := phi * KummerMorphism(E);
    end if;
    return C`KummerMorphism;
end intrinsic;

intrinsic WeierstrassModel(C::Crv) -> CrvEll, MapSch
    {Returns a Weierstrass model for an elliptic curve C,
    of the form y^2 + (a1*x + a3)*y = x^3 + a2*x^2 + a4*x + a6.}
    require IsEllipticCurve(C) :
	"Argument must be an elliptic curve model.";
    if Type(C) eq CrvEll then return C; end if;
    if not assigned C`WeierstrassMorphism then
	_, phi := EllipticCurve(C,Identity(C));
	C`WeierstrassMorphism := phi;
    end if;
    m := C`WeierstrassMorphism;
    return Codomain(m), m;
end intrinsic;

intrinsic WeierstrassMorphism(C::Crv) -> MapSch
    {}
    require IsEllipticCurve(C) :
	"Argument must be an elliptic curve model.";
    if Type(C) eq CrvEll then return IdentityMorphism(C); end if;
    if not assigned C`WeierstrassMorphism then
	_, phi := EllipticCurve(C,Identity(C));
	C`WeierstrassMorphism := phi;
    end if;
    return  C`WeierstrassMorphism;
end intrinsic;

intrinsic jInvariant(C::Crv) -> RngElt
    {}
    require IsEllipticCurve(C) :
	"Argument must be an elliptic curve model.";
    return jInvariant(WeierstrassModel(C));
end intrinsic;

intrinsic RandomPoint(C::Crv) -> Pt
    {A random point on an elliptic curve.}
    require IsEllipticCurve(C) :
        "Argument must be an elliptic curve model.";
    E, i := WeierstrassModel(C);
    bool, j := IsInvertible(i); assert bool;
    return j(Random(E));
end intrinsic;
