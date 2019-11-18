//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function NormalizePoint(P,prec)
    /*
    Given a projective point (or coordinate sequence) P over a Laurent series
    ring, return a scaled point in the integral power series ring.
    */
    P := Eltseq(P);
    z := Universe(P).1;
    rel_prec := Min([ AbsolutePrecision(f) : f in P ]);
    K := Universe(P);
    O := Type(K) eq RngSerPow select K else RingOfIntegers(Universe(P));
    v := -Min([ Valuation(f) : f in P ]);
    return [ O | (z^v + BigO(z^(rel_prec+v))) * f + BigO(z^prec) : f in P ];
end function;

function RandomTranslations(P,n : Bound := 256)
    /*
    Given a projective point (or coordinate sequence) P, return a sequence
    of n points obtained by evaluation at deformations of the form a1*q + a2*q^2.
    */
    P := Eltseq(P);
    O := Universe(P);
    q := O.1;
    prec := Min([ AbsolutePrecision(f) : f in P ]);
    pnts := [ ];
    p := Characteristic(O);
    if p eq 0 or p gt Bound then
        for i in [1..n] do
            a1 := Random([1..Bound]);
            a2 := Random([-Bound..Bound]);
            Append(~pnts, [ Evaluate(f,a1*q + a2*q^2 + BigO(q^prec)) + BigO(q^prec) : f in P ]);
        end for;
    else
        for i in [1..n] do
            s := Floor(Log(2,Bound));
            a := q + BigO(q^prec);
            for m in [2..s] do
                a +:= Random([0..p-1])*q^m;
            end for;
            Append(~pnts, [ Evaluate(f,a) + BigO(q^prec) : f in P ]);
        end for;
    end if;
    return pnts;
end function;

function FormalPoints(E,G,n)
    /*
    Given an elliptic curve E and subset (or subgroup) of points G,
    return a system of formal point in the neighborhood of T in G,
    to precision n.
    */
    xs, ys := FormalGroupExpansion(E,n);
    P := E(Parent(xs))![xs,ys,1];
    return [ P + T : T in G ];
end function;

intrinsic ExtendAdditionMorphism(E::Crv :
    BasisDimension := 0,
    ExtraPrecision := 0,
    NumberOfPoints := 8,
    ProjectionMorphism := 0,
    AdditionMorphismDegrees := [2,2],
    InterpolationPrecision := 16,
    TorsionOrder := 0) -> MapSch
    {}
    n := TorsionOrder;
    dim := BasisDimension;
    if dim eq 0 then dim := Length(Ambient(E)); end if;
    num := NumberOfPoints;
    prec0 := InterpolationPrecision;
    if ExtraPrecision eq 0 then
	extra_prec := 2*dim;
    else
	extra_prec := ExtraPrecision;
    end if;
    prec1 := InterpolationPrecision + extra_prec;
    if Type(E) eq CrvEll then
	E0 := E; iso_E0_E := Isomorphism(E,E,[0,0,0,1]);
    else
        require IsEllipticCurve(E): "Domain must be an elliptic curve.";
	E0, iso_E_E0 := WeierstrassModel(E);
	bool, iso_E0_E := IsInvertible(iso_E_E0); assert bool;
    end if;
    G0 := TorsionOrder eq 0 select [ E0!0 ] else DivisionPoints(E0!0,n);
    pnts_E := [ NormalizePoint(iso_E0_E(P),prec1) : P in FormalPoints(E0,G0,prec1) ];
    pnts_E := &cat[ RandomTranslations(P,Ceiling(num/#G0)) : P in pnts_E ];
    pnts_ExE := [ Pi cat Qi : Pi, Qi in pnts_E | Pi ne Qi ];
    mu := AdditionMorphism(E);
    pi := ProjectionMorphism;
    degs := AdditionMorphismDegrees;
    if Type(pi) eq MapSch then
	require Domain(pi) eq E : "Parameter \"ProjectionMorphism\" must have domain equal to the argument.";
	mu := mu * pi;
    end if;
    BB := MorphismInterpolation(mu, pnts_ExE[[1..num]], degs :
	Precision := prec0,
	BasisDimension := BasisDimension);
    require #BB gt 0 : "Addition morphism of given bidegree does not exist.";
    return map< Domain(mu)->Codomain(mu) | BB >;
end intrinsic;

intrinsic ExtendMorphism(phi::MapSch,deg::RngIntElt :
    TorsionOrder := 0,
    BasisDimension := 0,
    ExtraPrecision := 0,
    InterpolationPrecision := 16,
    NumberOfPoints := 1) -> MapSch
    {}
    return ExtendMorphism(phi,[deg] :
	TorsionOrder := TorsionOrder,
	BasisDimension := BasisDimension,
	ExtraPrecision := ExtraPrecision,
	InterpolationPrecision := InterpolationPrecision,
	NumberOfPoints := NumberOfPoints);
end intrinsic;

intrinsic ExtendMorphism(phi::MapSch,degs::[RngIntElt] :
    TorsionOrder := 0,
    BasisDimension := 0,
    ExtraPrecision := 0,
    InterpolationPrecision := 16,
    NumberOfPoints := 1) -> MapSch
    {Extend the given morphism (of an elliptic curve) by interpolating
    polynomials of the degree sequence degs. The degree sequence will
    be a singleton [d] if the domain is a simple projective space.}
    E := Domain(phi);
    n := TorsionOrder;
    dim := BasisDimension;
    if dim eq 0 then dim := Length(Ambient(E)); end if;
    num := NumberOfPoints;
    prec0 := InterpolationPrecision;
    if ExtraPrecision eq 0 then
	extra_prec := 2*dim;
    else
	extra_prec := ExtraPrecision;
    end if;
    prec1 := InterpolationPrecision + extra_prec;
    if Type(E) eq CrvEll then
	E0 := E; iso_E0_E := Isomorphism(E,E,[0,0,0,1]);
    else
        require IsEllipticCurve(E): "Domain must be an elliptic curve.";
	E0, iso_E_E0 := WeierstrassModel(E);
	bool, iso_E0_E := IsInvertible(iso_E_E0); assert bool;
    end if;
    G0 := TorsionOrder eq 0 select [ E0!0 ] else DivisionPoints(E0!0,n);
    pnts_E := [ NormalizePoint(iso_E0_E(P),prec1) : P in FormalPoints(E0,G0,prec1) ];
    pnts_E := &cat[ RandomTranslations(P,Ceiling(num/#G0)) : P in pnts_E ];
    BB := MorphismInterpolation(phi, pnts_E[[1..num]], degs :
	Precision := prec0,
	BasisDimension := BasisDimension);
    return map< E->Codomain(phi) | BB >;
end intrinsic;

intrinsic ExtendMorphismInverse(phi::MapSch, deg::RngIntElt :
    BasisDimension := 0,
    ExtraPrecision := 0,
    NumberOfPoints := 1,
    InterpolationPrecision := 16,
    TorsionOrder := 0) -> MapSch
    {}
    return ExtendMorphismInverse(phi, [deg] :
	BasisDimension := BasisDimension,
	ExtraPrecision := ExtraPrecision,
	InterpolationPrecision := InterpolationPrecision,
	NumberOfPoints := NumberOfPoints,
	TorsionOrder := TorsionOrder);
end intrinsic;

intrinsic ExtendMorphismInverse(phi::MapSch,degs::[RngIntElt] :
    BasisDimension := 0,
    ExtraPrecision := 0,
    InterpolationPrecision := 16,
    NumberOfPoints := 1,
    TorsionOrder := 0) -> MapSch
    {Extend the given morphism (of an elliptic curve) by interpolating
    polynomials of the degree sequence degs. The degree sequence will
    be a singleton [d] if the domain is a simple projective space.}
    E := Domain(phi);
    n := TorsionOrder;
    dim := BasisDimension;
    if dim eq 0 then dim := Length(Ambient(E)); end if;
    num := NumberOfPoints;
    prec0 := InterpolationPrecision;
    if ExtraPrecision eq 0 then
	extra_prec := 2*dim;
    else
	extra_prec := ExtraPrecision;
    end if;
    prec1 := InterpolationPrecision + extra_prec;
    if Type(E) eq CrvEll then
	E0 := E; iso_E0_E := Isomorphism(E,E,[0,0,0,1]);
    else
        require IsEllipticCurve(E): "Domain must be an elliptic curve.";
	E0, iso_E_E0 := WeierstrassModel(E);
	bool, iso_E0_E := IsInvertible(iso_E_E0); assert bool;
    end if;
    G0 := TorsionOrder eq 0 select [ E0!0 ] else DivisionPoints(E0!0,n);
    pnts_E := [ NormalizePoint(iso_E0_E(P),prec1) : P in FormalPoints(E0,G0,prec1) ];
    pnts_E := &cat[ RandomTranslations(P,Ceiling(num/#G0)) : P in pnts_E ];
    BB := MorphismInverseInterpolation(phi, pnts_E[[1..num]], degs :
	Precision := prec0,
	BasisDimension := BasisDimension);
    return map< Codomain(phi)->E | BB >;
end intrinsic;

intrinsic ExtendMorphismPushThrough(phi::MapSch, psi::MapSch, deg::RngIntElt :
    TorsionOrder := 0,
    BasisDimension := 0,
    ExtraPrecision := 0,
    NumberOfPoints := 1,
    InterpolationPrecision := 16) -> MapSch
    {}
    return ExtendMorphismPushThrough(phi, psi, [deg] :
	BasisDimension := BasisDimension,
	ExtraPrecision := ExtraPrecision,
	NumberOfPoints := NumberOfPoints,
	InterpolationPrecision := InterpolationPrecision,
	TorsionOrder := TorsionOrder);
end intrinsic;

intrinsic ExtendMorphismPushThrough(phi::MapSch, psi::MapSch, degs::[RngIntElt] :
    BasisDimension := 0,
    ExtraPrecision := 0,
    NumberOfPoints := 1,
    InterpolationPrecision := 16,
    TorsionOrder := 0) -> MapSch
    {Compute the defining polynomials of degrees degs for the morphism
    rho (of an elliptic curve) such that phi * rho = psi by interpolating
    polynomials (in phi(P)) of the degree sequence degs. The degree
    sequence will be a singleton [d] if the domain is a simple projective
    space.}
    E := Domain(phi);
    n := TorsionOrder;
    dim := BasisDimension;
    if dim eq 0 then dim := Length(Ambient(E)); end if;
    num := NumberOfPoints;
    prec0 := InterpolationPrecision;
    if ExtraPrecision eq 0 then
	extra_prec := 2*dim;
    else
	extra_prec := ExtraPrecision;
    end if;
    prec1 := InterpolationPrecision + extra_prec;
    if Type(E) eq CrvEll then
	E0 := E; iso_E0_E := Isomorphism(E,E,[0,0,0,1]);
    else
	require IsEllipticCurve(E): "Domain must be an elliptic curve.";
	E0, iso_E_E0 := WeierstrassModel(E);
	bool, iso_E0_E := IsInvertible(iso_E_E0); assert bool;
    end if;
    G0 := TorsionOrder eq 0 select [ E0!0 ] else DivisionPoints(E0!0,n);
    pnts_E := [ NormalizePoint(iso_E0_E(P),prec1) : P in FormalPoints(E0,G0,prec1) ];
    pnts_E := &cat[ RandomTranslations(P,Ceiling(num/#G0)) : P in pnts_E ];
    BB := MorphismPushThroughInterpolation(phi, psi, pnts_E[[1..num]], degs :
	Precision := prec0,
	BasisDimension := BasisDimension);
    // print "Codomain(psi):"; Codomain(psi);
    // print "Codomain(phi):"; Codomain(phi);
    return map< Codomain(psi)->Codomain(phi) | BB >;
end intrinsic;

