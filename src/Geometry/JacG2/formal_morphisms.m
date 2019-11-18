//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                   Morphisms of Formal Groups                             //
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

forward EllipticFormalLogarithm;

//////////////////////////////////////////////////////////////////////////////

declare type HomGrpFrml[MapGrpFrml];

declare attributes HomGrpFrml:
    Domain,
    Codomain,
    Logarithm;

declare attributes MapGrpFrml:
    Element,
    Parent;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                            Creation functions                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Hom(G1::GrpFrml,G2::GrpFrml) -> HomGrpFrml
    {}
    M := New(HomGrpFrml);
    M`Domain := G1;
    M`Codomain := G2;
    return M;
end intrinsic;

intrinsic FormalLogarithm(G::GrpFrml) -> MapGrpFrml
    {}
    E := G`GeometricObject;
    p := Characteristic(BaseRing(E));
    require Type(E) eq CrvEll :
	"Argument must be the formal group of an elliptic curve.";
    require p eq 0 : "Base ring of argument must be characteristic 0.";
    return EllipticFormalLogarithm(G);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                              Coercions                                   //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic IsCoercible(M::HomGrpFrml,f::.) -> BoolElt, MapGrpFrml
    {Coerce the element f into the set M of formal group morphisms.}
    if Type(f) eq MapGrpFrml and Parent(f) eq M then
	return true, f;
    end if;
    return false, "Invalid coercion.";
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                                  Printing                                //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Print(M::HomGrpFrml, level::MonStgElt)
    {}
    printf "Morphisms of %o to %o", M`Domain, M`Codomain;
end intrinsic;

intrinsic Print(x::MapGrpFrml, level::MonStgElt)
    {}
    printf "%o", x`Element;
end intrinsic;


//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         Membership and Equality                          //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., X::HomGrpFrml) -> BoolElt
   {Returns true if x is in X.}
   if Type(x) eq MapGrpFrml then
      return x`Parent eq X;
   end if;
   return false;
end intrinsic;

intrinsic Parent(x::MapGrpFrml) -> HomGrpFrml
   {}
   return x`Parent;
end intrinsic;

intrinsic 'eq' (M1::HomGrpFrml,M2::HomGrpFrml) -> BoolElt
   {True iff the two sets of morphisms of formal groups are equal.}
   return M1`Domain cmpeq M2`Domain and M1`Codomain cmpeq M2`Codomain;
end intrinsic;

intrinsic 'eq' (x::MapGrpFrml,y::MapGrpFrml) -> BoolElt
   {True iff the two formal group morphisms are equal.}
   return Parent(x) eq Parent(y) and x`Element eq y`Element;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                               Attributes                                 //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic Domain(f::MapGrpFrml) -> GrpFrml
    {}
    return f`Parent`Domain;
end intrinsic;

intrinsic Codomain(f::MapGrpFrml) -> GrpFrml
    {}
    return f`Parent`Codomain;
end intrinsic;

intrinsic Domain(M::HomGrpFrml) -> GrpFrml
    {}
    return M`Domain;
end intrinsic;

intrinsic Codomain(M::HomGrpFrml) -> GrpFrml
    {}
    return M`Codomain;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                         Elliptic Curve Isogenies                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic '+' (f::MapGrpFrml,g::MapGrpFrml : Precision := 0) -> BoolElt
    {}
    M := f`Parent;
    require M eq g`Parent : "Arguments must have the same parent.";
    G := M`Codomain;
    prec := Precision eq 0 select G`Precision else Precision;
    F := FormalGroupLaw(G,prec);
    h := New(MapGrpFrml);
    h`Parent := M;
    h`Element := Evaluate(F,[f`Element,g`Element]);
    return h;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                          Elliptic Formal Logarithm                       //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function EllipticFormalLogarithm(G)
    // precision ignored
    E := G`GeometricObject;
    // induce computation of series
    F := FormalGroupLaw(G,G`Precision : UsePowerSeries);
    a1,a2,a3,a4,a6 := Explode(Eltseq(E));
    u := Parent(G`SSeries).1;
    ss := G`SSeries;
    ys := -1/ss;
    xs := u/ss;
    u := Parent(xs).1;
    w := Derivative(xs)/(a3+a1*xs+2*ys);
    return Integral(w);
end function;

// ??? EllipticFormalExponential ???

//////////////////////////////////////////////////////////////////////////////
