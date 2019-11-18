//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//    Copyright (C) 2010-2015 David Kohel <David.Kohel@univ-amu.fr>         //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
These are potential global synonyms ("model" == "normal form"), but
Magma doesn't export local definitions. The syntax "normal form" is
given preference in this file.

// Degree 3 models:
EllipticCurve_Triangular_Model := EllipticCurve_Triangular_NormalForm;
EllipticCurve_Symmetric_Triangular_Model := EllipticCurve_Symmetric_Triangular_NormalForm;
EllipticCurve_Hessian_Model := EllipticCurve_Hessian_NormalForm;
EllipticCurve_Twisted_Hessian_Model := EllipticCurve_Twisted_Hessian_NormalForm;
EllipticCurve_Huff_Model := EllipticCurve_Huff_NormalForm;
// Degree 4 models:
EllipticCurve_Edwards_Model := EllipticCurve_Edwards_NormalForm;
EllipticCurve_Twisted_Edwards_Model := EllipticCurve_Twisted_Edwards_NormalForm;
EllipticCurve_Edwards_Model := EllipticCurve_Edwards_NormalForm;
EllipticCurve_Mu4_Model := EllipticCurve_Mu4_NormalForm;
EllipticCurve_Semisplit_Mu4_Model := EllipticCurve_Semisplit_Mu4_NormalForm;
EllipticCurve_Split_Mu4_Model := EllipticCurve_Split_Mu4_NormalForm;
EllipticCurve_Twisted_Semisplit_Mu4_Model := EllipticCurve_Twisted_Semisplit_Mu4_NormalForm;
EllipticCurve_Twisted_Split_Mu4_Model := EllipticCurve_Twisted_Split_Mu4_NormalForm;
EllipticCurve_Jacobi_Model := EllipticCurve_Jacobi_NormalForm;
EllipticCurve_C4_Model := EllipticCurve_C4_NormalForm;
EllipticCurve_Z4_Model := EllipticCurve_C4_NormalForm;
EllipticCurve_Z4_NormalForm := EllipticCurve_C4_NormalForm;
EllipticCurve_Semisplit_C4_Model := EllipticCurve_Semisplit_C4_NormalForm;
EllipticCurve_Semisplit_Z4_Model := EllipticCurve_Semisplit_C4_NormalForm;
EllipticCurve_Semisplit_Z4_NormalForm := EllipticCurve_Semisplit_C4_NormalForm;
EllipticCurve_Twisted_C4_Model := EllipticCurve_Twisted_C4_NormalForm;
EllipticCurve_Twisted_Z4_Model := EllipticCurve_Twisted_C4_NormalForm;
EllipticCurve_Twisted_Z4_NormalForm := EllipticCurve_Twisted_C4_NormalForm;
EllipticCurve_Split_C4_Model := EllipticCurve_Split_C4_NormalForm;
EllipticCurve_Split_Z4_Model := EllipticCurve_Split_C4_NormalForm;
EllipticCurve_Split_Z4_NormalForm := EllipticCurve_Split_C4_NormalForm;
*/

function HasCommonField(a,b)
    if Type(a) eq RngIntElt and Type(b) eq RngIntElt then
        K := RationalField();
        a := K!a; b := K!b;
    end if;
    K := Parent(a);
    bool, b := IsCoercible(K,b);
    K := Parent(b);
    bool, a := IsCoercible(K,a);
    return bool, K, a, b;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Hessian models
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Hessian_NormalForm(d::RngElt) -> Crv
    {The Hessian model in PP^2 for an elliptic curve, given by
    X0^3 + X1^3 + X2^3 = d*X0*X1*X2, with identity (0:1:-1).}
    require d^3 ne 27: "Argument 2 must not satisfy d^3 = 27.";
    K := Parent(d);
    if Type(K) eq RngInt then K := RationalField(); end if;
    return EllipticCurve_Twisted_Hessian_NormalForm(K!1,d);
end intrinsic;

intrinsic EllipticCurve_Hessian_NormalForm(PP::Prj,d::RngElt) -> Crv
    {The Hessian model in PP for an elliptic curve, given by
    X0^3 + X1^3 + X2^3 = d*X0*X1*X2, with identity (0:1:-1).}
    require Dimension(PP) eq 2 :
        "Argument 1 must be a projective space of dimension 2.";
    KK := BaseRing(PP);
    bool, d := IsCoercible(KK,d);
    require bool: "Argument 2 must coerce into the base ring of argument 1.";
    require d^3 ne 27: "Argument 2 must not satisfy d^3 = 27.";
    return EllipticCurve_Twisted_Hessian_NormalForm(PP,KK!1,d);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Twisted Hessian models
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Hessian_NormalForm(a::RngElt,d::RngElt) -> Crv
    {The twisted Hessian model in PP^2 for an elliptic curve, given by
    a*X0^3 + X1^3 + X2^3 = d*X0*X1*X2, with identity (0:1:-1).}
    K := Parent(d);
    if Type(K) eq RngInt then
        K := RationalField(); d := RationalField()!d;
    end if;
    bool, a := IsCoercible(K,a);
    if not bool then
        bool, d := IsCoercible(K,d);
    end if;
    require bool: "Arguments must be coercible into a common parent.";
    PP<X0,X1,X2> := ProjectiveSpace(K,2);
    return EllipticCurve_Twisted_Hessian_NormalForm(PP,a,d);
end intrinsic;

intrinsic EllipticCurve_Twisted_Hessian_NormalForm(PP::Prj,a::RngElt,d::RngElt) -> Crv
    {The twisted Hessian model in PP for an elliptic curve, given
    by a*X0^3 + X1^3 + X2^3 = d*X0*X1*X2, with identity (0:1:-1).}
    require Dimension(PP) eq 2: "Argument 1 must be a projective space of dimension 2.";
    K := BaseRing(PP);
    bool, a := IsCoercible(K,a);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    bool, d := IsCoercible(K,d);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    require a ne 0 and d^3 ne 27*a :
        "Arguments 2 and 3 must be different from [0,*] and [d^3,3*d].";
    X0, X1, X2 := Explode([ PP.i : i in [1..3] ]);
    H := Curve(PP,a*X0^3+X1^3+X2^3-d*X0*X1*X2);
    H`EllipticModelType := "Hessian";
    H`EllipticModelInvariants := [a,d];
    H`IdentityElement := H![0,-1,1];
    H`EmbeddingClass := H![0,-1,1];
    H`InverseMorphism := map< H->H | [X0,X2,X1] >;
    H`KummerMorphism := map< H->Curve(ProjectiveSpace(K,1)) |
        [ [X0,X1+X2], [ d*X0*X2 - X1^2 + X1*X2 - X2^2, a*X0^2 + d*X2^2 ] ] >;
    E := EllipticCurve([d,0,9*a,-9*a*d,-a*(d^3 + 27*a)]);
    P2<X,Y,Z> := AmbientSpace(E);
    H`WeierstrassMorphism := map< H->E |
        [ -(9*a*X0 + d^2*(X1 + X2)), (d^3 - 27*a)*X1, d*X0 + 3*(X1 + X2) ],
        [ 3*X + d^2*Z, Y, -d*X - Y - 9*a*Z ] >;
    HxH := ProductScheme(H,H);
    PPxPP<X0,X1,X2,Y0,Y1,Y2> := AmbientSpace(HxH);
    B := [
        [ X0^2*Y1*Y2 - X1*X2*Y0^2, X2^2*Y0*Y1 - X0*X1*Y2^2, X1^2*Y0*Y2 - X0*X2*Y1^2 ],
        [ X0*X1*Y1^2 - X2^2*Y0*Y2, a*X0*X2*Y0^2 - X1^2*Y1*Y2, X1*X2*Y2^2 - a*X0^2*Y0*Y1 ],
        [ X0*X2*Y2^2 - X1^2*Y0*Y1, X1*X2*Y1^2 - a*X0^2*Y0*Y2, a*X0*X1*Y0^2 - X2^2*Y1*Y2 ]
        ];
    H`AdditionMorphism := map< HxH->H | B >;
    H`EmbeddingClass := [0,-1,1];
    return H;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Triangular model
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Triangular_NormalForm(b::RngElt,c::RngElt) -> Crv
    {}
    bool, K, b, c := HasCommonField(b,c);
    require bool: "Arguments must be coercible into a common parent.";
    require IsUnit(b): "Argument 1 must be a unit.";
    require IsUnit(c): "Argument 2 must be a unit.";
    return EllipticCurve([b,0,c,0,0]);
end intrinsic;

intrinsic EllipticCurve_Triangular_NormalForm(PP::Prj,b::RngElt,c::RngElt) -> Crv
    {Returns a triangular elliptic curve of the form Y^2Z + (bX + cZ)Y = X^3 in PP.}
    require Dimension(PP) eq 2: "Argument 1 must be a projective plane.";
    K := BaseField(PP);
    bool, b := IsCoercible(K,b);
    require bool: "Argument 2 must be coercible to the base ring of argument 1.";
    bool, c := IsCoercible(K,c);
    require bool: "Argument 3 must be coercible to the base ring of argument 1.";
    require IsUnit(b): "Argument 2 must be a unit.";
    require IsUnit(c): "Argument 3 must be a unit.";
    return PP!!EllipticCurve([b,0,c,0,0]);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Symmetric triangular model
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Symmetric_Triangular_NormalForm(r::RngElt,s::RngElt) -> Crv
    {}
    bool, K, r, s := HasCommonField(r,s);
    require bool: "Arguments must be coercible into a common parent.";
    require IsUnit(r): "Argument 1 must be a unit.";
    require IsUnit(s): "Argument 2 must be a unit.";
    PP<X,Y,Z,W> := ProjectiveSpace(K,3);
    return EllipticCurve_Symmetric_Triangular_NormalForm(PP,r,s);
end intrinsic;

intrinsic EllipticCurve_Symmetric_Triangular_NormalForm(PP::Prj,r::RngElt,s::RngElt) -> Crv
    {Returns a symmetric triangular model X^3 = rYZW X = s(Y + Z + W)
    of an elliptic curve, with base point (0:1:0:-1).}
    K := BaseRing(PP);
    bool, r := IsCoercible(K,r);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    bool, s := IsCoercible(K,s);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    require IsUnit(r): "Argument 2 must be a unit.";
    require IsUnit(s): "Argument 3 must be a unit.";
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    X,Y,Z,W := Explode([ PP.i : i in [1..4] ]);
    SS := Curve(PP,[X^3 - r*Y*Z*W, X - s*(Y + Z + W)]);
    SS`EllipticModelType := "Symmetric triangular";
    SS`EllipticModelInvariants := [r,s];
    SS`IdentityElement := [0,1,0,-1];
    SS`EmbeddingClass := [0,1,0,-1];
    SS`InverseMorphism := map< SS->SS | [X,W,Z,Y] >;
    SS`KummerMorphism := map< SS->Curve(ProjectiveSpace(K,1)) | [X,Z] >;
    EE := EllipticCurve_Triangular_NormalForm([1/s,1/r]);
    SS`WeierstrassMorphism := map< SS->EE | [-X,Y,r*Z] >;
    SSxSS := ProductScheme(SS,SS);
    PPxPP<X1,Y1,Z1,W1,X2,Y2,Z2,W2> := Ambient(SSxSS);
    // Exceptional divisor 3*Delta on SS:
    B0 := [
        s*r*(W1*(Z1*Y2^2 + (Y1*Z2 - W1*Y2)*Z2) - (Z1^2*Y2 + Y1*(Y1*Z2 - Z1*W2))*W2),
        3*X1*X2*(W1*X2 - X1*W2) + r*(Y1*Z1*W2^2 - W1^2*Y2*Z2),
        3*X1*X2*(Z1*X2 - X1*Z2) + r*(Y1*W1*Z2^2 - Z1^2*Y2*W2),
        3*X1*X2*(Y1*X2 - X1*Y2) + r*(Z1*W1*Y2^2 - Y1^2*Z2*W2) ];
    // Exceptional divisor 3*Delta + (O,-T) on SS:
    B1 := [
        s*r*(Z1*(Y1*Y2^2 - Z1*Y2*Z2 + W1*Z2^2) - (Y1^2*Y2 + W1*(W1*Z2 - Y1*W2))*W2),
        3*X1*X2*(Y1*X2 - X1*Z2) + r*(Z1*W1*Z2^2 - Y1^2*Y2*W2),
        3*X1*X2*(W1*X2 - X1*Y2) + r*(Y1*Z1*Y2^2 - W1^2*Z2*W2),
        3*X1*X2*(Z1*X2 - X1*W2) - r*(Z1^2*Y2*Z2 - Y1*W1*W2^2) ];
    // Exceptional divisor 3*Delta + (O,+T) on SS:
    B2 := [
        s*r*(Y1*(W1*Y2^2 - (Y1*Y2 - Z1*Z2)*Z2) - (W1^2*Y2 + Z1*(Z1*Z2 - W1*W2))*W2),
        3*X1*X2*(Z1*X2 - X1*Y2) + r*(Y1*W1*Y2^2 - Z1^2*Z2*W2),
        3*X1*X2*(Y1*X2 - X1*W2) - r*(Y1^2*Y2*Z2 - Z1*W1*W2^2),
        3*X1*X2*(W1*X2 - X1*Z2) + r*(Y1*Z1*Z2^2 - W1^2*Y2*W2) ];
    SS`AdditionMorphism := map< SSxSS->SS | [B0,B1,B2] >;
    return SS;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Huff model -- Not very interesting to have a degree 3 model with level 2
// structure? E.g. the translation maps (by 2-torsion) is nonlinear.
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Huff_NormalForm(a::RngElt,b::RngElt) -> Crv
    {}
    bool, K, a, b := HasCommonField(a,b);
    require bool: "Arguments must be coercible into a common parent.";
    require IsUnit(K!2): "Two must be a unit in the base ring of argument 1.";
    require IsUnit(a): "Argument 1 must be a unit.";
    require IsUnit(b): "Argument 2 must be a unit.";
    PP<X0,X1,X2> := ProjectiveSpace(K,2);
    return EllipticCurve_Huff_NormalForm(PP,a,b);
end intrinsic;

intrinsic EllipticCurve_Huff_NormalForm(PP::Prj,a::RngElt,b::RngElt) -> Crv
    {An elliptic curve in Huff normal form, given by
    a X1 (X0^2 - X2^2) = b X2 (X0^2 - X1^2)) with identity (1:0:0).}
    K := BaseRing(PP);
    require Dimension(PP) eq 2: "Argument 1 must be a projective space of dimension 2.";
    require IsUnit(K!2): "Two must be a unit in the base ring of argument 1.";
    bool, a := IsCoercible(K,a);
    require bool: "Argument 2 must be compatible with base ring of argument 1.";
    bool, b := IsCoercible(K,b);
    require bool: "Argument 3 must be compatible with base ring of argument 1.";
    require IsUnit(a): "Argument 2 must be a unit.";
    require IsUnit(b): "Argument 3 must be a unit.";
    X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    C := Curve(PP,a*X1*(X0^2 - X2^2) - b*X2*(X0^2 - X1^2));
    C`IdentityElement := [1,0,0];
    C`EmbeddingClass := [1,0,0];
    C`InverseMorphism := map< C->C | [X0,-X1,-X2] >;
    E := EllipticCurve([0,a^2+b^2,0,a^2*b^2,0]);
    P2<X,Y,Z> := AmbientSpace(E);
    C`WeierstrassMorphism := map< C->E |
        [ a*b*(a*X2 - b*X1), a*b*(a^2 - b^2)*X0, (a*X1 - b*X2) ],
        [ Y, b*(X + a^2*Z),     a*(X + b^2*Z) ] >;
    C`EllipticModelType := "Huff normal form";
    C`EllipticModelInvariants := [a,b];
    CxC := ProductScheme(C,2);
    PPxPP<X0,X1,X2,Y0,Y1,Y2> := AmbientSpace(CxC);
    /*
    // From Joye, Tichouchi, Vergnaud, a bidegree (4,4)-addition law:
    Z1, X1, Y1, Z2, X2, Y2 := Explode([X0,X1,X2,Y0,Y1,Y2]);
    C`AdditionMorphism := map< CxC->C |
        [
        -(X1*X2 - Z1*Z2)*(X1*X2 + Z1*Z2)*(Y1*Y2 - Z1*Z2)*(Y1*Y2 + Z1*Z2),
        (X1*Z2 + Z1*X2)*(X1*X2 - Z1*Z2)*(Y1*Y2 + Z1*Z2)^2,
        (Y1*Z2 + Z1*Y2)*(Y1*Y2 - Z1*Z2)*(X1*X2 + Z1*Z2)^2
        ] >;
    // However, the exceptional divisor is large.
    PPxPP<X0,X1,X2,Y0,Y1,Y2> := PPxPP;
    */
    E, iso_C_E := EllipticCurve_Semisplit_C4_NormalForm(C,C![1,1,1],C![0,0,1]);
    iso_E_C := Inverse(iso_C_E);
    mu_E := AdditionMorphism(E);
    xx := [ X0, X1, X2 ]; yy := [ Y0, Y1, Y2 ];
    B_C_E := AllDefiningPolynomials(iso_C_E);
    iso_CxC_ExE := map< CxC->Domain(mu_E) |
        [ [ f(xx) : f in S1 ] cat [ f(yy) : f in S2 ] : S1, S2 in B_C_E ] >;
    C`AdditionMorphism := iso_CxC_ExE * mu_E * iso_E_C;
    return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Edwards models (as one type which includes twisted Edwards)
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Edwards_NormalForm(d::RngElt) -> Crv
    {}
    K := Parent(d);
    if Type(K) eq RngInt then K := RationalField(); end if;
    require IsUnit(K!2): "Two must be a unit in the parent of the argument.";
    require d ne 0 and d ne 1: "Argument must be different from 0 and 1.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Twisted_Edwards_NormalForm(PP,d,1);
end intrinsic;

intrinsic EllipticCurve_Edwards_NormalForm(PP::Prj,d::RngElt) -> Crv
    {The Edwards model in PP (= PP^3) for an elliptic curve, given by
    X0^2 + d*X3^2 = X1^2 + X2^2, X0*X3 = X1*X2, with identity (1:0:1:0).}
    K := BaseRing(PP);
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    require IsUnit(K!2): "Two must be a unit in the base ring of argument 1.";
    bool, d := IsCoercible(K,d);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require d ne 0 and d ne 1: "Argument 2 must be different from 0 and 1.";
    return EllipticCurve_Twisted_Edwards_NormalForm(PP,d,1);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Edwards_NormalForm(d::RngElt,a::RngElt) -> Crv
    {}
    K := Parent(d);
    if Type(K) eq RngInt then K := RationalField(); end if;
    bool, a := IsCoercible(K,a);
    require bool: "Argument 2 must be coercible to the parent of argument 1.";
    require a ne 0 and d ne 0 and d ne a: "Arguments must be nonzero and distinct.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Twisted_Edwards_NormalForm(PP,d,a);
end intrinsic;

intrinsic EllipticCurve_Twisted_Edwards_NormalForm(PP::Prj,d::RngElt,a::RngElt) -> Crv
    {The twisted Edwards model in PP (= PP^3) for an elliptic curve, given by
    X0^2 + d*X3^2 = a*X1^2 + X2^2, X0*X3 = X1*X2, with identity (1:0:1:0).}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    require IsUnit(K!2): "Two must be a unit in the base ring of argument 1.";
    bool, d := IsCoercible(K,d);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    bool, a := IsCoercible(K,a);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    require d ne 0 and a ne 0 and d ne a :
        "Arguments 2 and 3 must be nonzero and distinct.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    E := Curve(PP,[X0^2 + d*X3^2 - a*X1^2 - X2^2, X0*X3 - X1*X2]);
    if a eq 1 then
        E`EllipticModelType := "Edwards normal form";
    else
        // If this is changed to "Twisted Edwards normal form",
        // then one must also modify the corresponding lines
        // in elliptic_transformations.m
        E`EllipticModelType := "Edwards normal form";
    end if;
    E`EllipticModelInvariants := [d,a];
    // Install the identity and [-1]:
    E`IdentityElement := [1,0,1,0];
    E`EmbeddingClass := [-1,0,1,0];
    E`InverseMorphism := map< E->E | [-X0,X1,-X2,X3] >;
    E`KummerMorphism := map< E->Curve(ProjectiveSpace(K,1)) | [[X0,X2],[X1,X3]] >;
    P2<X,Y,Z> := ProjectiveSpace(K,2);
    if a eq 1 then
        // This model is linear in d with a 4-torsion point at (0,0)
        // [and is integral for the parametrization by d = 1-16*c]:
        E0 := P2!!EllipticCurve([1,(1-d)/16,(1-d)/16,0,0]);
        BB_EE_E0 := [4*(1-d)*X3, (1-d)*(X0 - X1 + X2 - X3), 32*(X1 - X3)];
        E`WeierstrassMorphism := map< E->E0 | BB_EE_E0 >;
        // This model has divisor d-1 of discriminant in coefficients, with
        // a 2-torsion point at (0,0) and 4-torsion point at (-d+1,0):
        E0 := P2!!EllipticCurve([4,2*(d-1),0,(d-1)^2,0]);
        E`WeierstrassMorphism := map< E->E0 | [
            (d-1)*(X1 + X3), -2*(d-1)*(X0 + X1 + X2 + X3), -X1 + X3 ] >;
        // This diagonalized model specializes the twisted model to a = 1:
        E0 := P2!!EllipticCurve([0,2*(d+1),0,(d-1)^2,0]);
        BB_EE_E0 := [-(d-1)*(X1+X3), 2*(d-1)*(X0+X2), X1-X3];
        BB_E0_EE := [[
            (d-1)*((X+(d-1)*Z)^2+4*X*Z)-Y^2,
            2*Y*(X-(d-1)*Z),
            (1-d)*((X+(d-1)*Z)^2+4*X*Z)-Y^2,
            2*Y*(X+(d-1)*Z)],
            [Y*(X-(d-1)*Z),-2*X*(X-(d-1)*Z),Y*(X+(d-1)*Z),-2*X*(X+(d-1)*Z)]];
        E`WeierstrassMorphism := map< E->E0 | BB_EE_E0, BB_E0_EE >;
    else
        // This model has is diagonalized with a 2-torsion point at (0,0):
        E0 := P2!!EllipticCurve([0,2*(d+a),0,(d-a)^2,0]);
        BB_EE_E0 := [-(d-a)*(X1+X3), 2*(d-a)*(X0+X2), X1-X3];
        BB_E0_EE := [[
            (d-a)*((X+(d-a)*Z)^2+4*a*X*Z)-Y^2,
            2*Y*(X-(d-a)*Z),
            (a-d)*((X+(d-a)*Z)^2+4*a*X*Z)-Y^2 ,
            2*Y*(X+(d-a)*Z)
            ],
            [Y*(X-(d-a)*Z),-2*X*(X-(d-a)*Z),Y*(X+(d-a)*Z),-2*X*(X+(d-a)*Z)]];
        E`WeierstrassMorphism := map< E->E0 | BB_EE_E0, BB_E0_EE >;
    end if;
    // Install the addition morphism:
    ExE := ProductScheme(E,E);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(ExE);
    BB_1 := [[a*X1*Y1 + X2*Y2, X0*Y3 + X3*Y0],[X0*Y0 + d*X3*Y3, X1*Y2 + X2*Y1]];
    BB_2 := [[X1*Y2 - X2*Y1, -X0*Y3 + X3*Y0],[X0*Y0 - d*X3*Y3, -a*X1*Y1 + X2*Y2]];
    BB := [[ S1[i]*S2[j] : i in [1,2], j in [1,2] ] : S1 in BB_1, S2 in BB_2];
    E`AdditionMorphism := map< ExE->E | BB >;
    // Finished installation of group structure.
    return E;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Split Edwards models (original model of Edwards)
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Split_Edwards_NormalForm(a::RngElt) -> Crv
    {}
    K := Parent(a);
    if Type(K) eq RngInt then K := RationalField(); end if;
    require a ne 0 and a^2 notin {K|1,-1} :
        "Argument must be neither 0 nor a fourth root of 1.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Split_Edwards_NormalForm(PP,a);
end intrinsic;

intrinsic EllipticCurve_Split_Edwards_NormalForm(PP::Prj,a::RngElt) -> Crv
    {The split Edwards model (embedded in PP [= PP^3]) for
    an elliptic curve, as originally defined by Edwards:
    a^2 (X0^2 + X3^2) = X1^2 + X2^2, X0*X3 = X1*X2, with
    identity (1:0:a:0). N.B. Edwards defined his normal
    form by the affine curve x^2 + y^2 = a^2 (1 + z^2),
    where z = xy, which embeds in projective 3-space as
    (1:x:y:z).}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    require IsUnit(K!2): "Two must be a unit in the base ring of argument 1.";
    bool, a := IsCoercible(K,a);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    require a ne 0 and a^2 notin {K|1,-1} :
        "Argument 2 must be neither 0 nor a fourth root of 1.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    E := Curve(PP,[a^2*(X0^2 + X3^2) - X1^2 - X2^2, X0*X3 - X1*X2]);
    E`EllipticModelType := "Split Edwards normal form";
    E`EllipticModelInvariants := [a];
    // Install the identity and [-1]:
    E`IdentityElement := [1,0,a,0];
    E`EmbeddingClass := [-1,0,a,0];
    E`InverseMorphism := map< E->E | [-X0,X1,-X2,X3] >;
    E`KummerMorphism := map< E->Curve(ProjectiveSpace(K,1)) | [[X0,X2],[X1,X3]] >;
    E0 := EllipticCurve([1,-(a^4-1)/16,-(a^4-1)/16,0,0]);
    P2<X,Y,Z> := AmbientSpace(E0);
    BB_E_E0 := [ (a^4-1)/(4*a)*X3, (a^4-1)/16*(a*X0 - X1 + X2 - 1/a*X3), -2*(X1 - 1/a*X3) ];
    BB_E0_E := [
        X^2 + 2*X*Y - (a^4-1)/16*(3*X + 4*Y - (a^4-1)/8*Z)*Z,
        a*(X - (a^4-1)/8*Z)*(X - (a^4-1)/16*Z),
        a*X*(X + 2*Y - (a^4-1)/16*Z),
        a^2*X*(X-(a^4-1)/16*Z) ];
    E`WeierstrassMorphism := map< E->E0 | BB_E_E0, BB_E0_E >;
    // Install the addition morphism:
    ExE := ProductScheme(E,E);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(ExE);
    BB_1 := [[X1*Y1 + X2*Y2, a*(X0*Y3 + X3*Y0)], [a*(X0*Y0 + X3*Y3), X1*Y2 + X2*Y1]];
    BB_2 := [[X2*Y1 - X1*Y2, a*(X0*Y3 - X3*Y0)], [a*(X0*Y0 - X3*Y3), X2*Y2 - X1*Y1]];
    BB := [[ S1[i]*S2[j] : i in [1,2], j in [1,2] ] : S1 in BB_1, S2 in BB_2];
    E`AdditionMorphism := map< ExE->E | BB >;
    // Finished installation of group structure.
    return E;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

// This gives a good model for the 'original' canonical model of level 4
// in my 'Addition laws...' paper which  did not have good reduction at 2.
// A coordinate rescaling by 4 gives the mu_4-normal form.

intrinsic EllipticCurve_Mu4_NormalForm(r::RngElt) -> Crv
    {}
    K := Parent(r);
    if Type(K) eq RngInt then K := RationalField(); r := K!r; end if;
    require IsUnit(r) and 16*r ne 1: "Argument must be a unit and not 1/16.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Mu4_NormalForm(PP,r);
end intrinsic;

intrinsic EllipticCurve_Mu4_NormalForm(PP::Prj,r::RngElt) -> Crv
    {An elliptic curve in mu_4 normal form defined by
    X0^2 - r*X2^2 = X1*X3, and X1^2 - X3^2 = X0*X2,
    and identity O = (1:1:0:1),
    corresponding to the canonical model of level 4 in
    "Addition law structure of elliptic curves", with
    the change of variables X2 <- 4*X2 and 16*r = d
    (Edwards curve parameter), in order to
    have good reduction at 2.}
    K := BaseRing(PP);
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    bool, r := IsCoercible(K,r);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(r) and 16*r ne 1: "Argument 2 must be a unit and not 1/16.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    C := Curve(PP,[X0^2-r*X2^2-X1*X3,X1^2-X3^2-X0*X2]);
    C`EllipticModelType := "Mu_4 normal form";
    C`EllipticModelInvariants := [r];
    C`IdentityElement := C![1,1,0,1];
    C`EmbeddingClass := [1,-1,0,-1];
    C`InverseMorphism := map< C->C | [X0,X3,-X2,X1] >;
    C`KummerMorphism := map< C->Curve(ProjectiveSpace(K,1)) | [[X0,X1+X3],[X1-X3,X2]] >;
    E := EllipticCurve([1,-8*r,0,(16*r - 6)*r,(4*r - 1)*r]);
    C`WeierstrassMorphism := map< C->E | [
        (8*r - 1)*(X1 - X3) + 4*r*X2,
        -(16*r - 1)*(X0 + X1) + 2*r*(2*(X1 - X3) - X2),
        2*(X1 - X3) - X2
        ] >;
    E := EllipticCurve([1,4*r,0,-4*r,-16*r^2-r]);
    P2<X,Y,Z> := AmbientSpace(E);
    if Characteristic(K) eq 2 then
        BB_C_E := [X1 + X3, X0 + X1, X2];
        F := X^2 + Y*Z; G := Y^2 + r*Z^2;
        BB_E_C := [ [X^2, F, Z^2, F + X*Z], [G + X*Y, G, X*Z, G + X^2] ];
    else
        SymMu4 := func< A, B | [2*A[1]*B[1], A[2]*B[1]+A[1]*B[2], 2*A[2]*B[2], A[2]*B[1]-A[1]*B[2]] >;
        BB_C_E := [X1 - 8*r*X2 - X3, (16*r - 1)*X0 + (8*r - 1)*X1 + 4*r*X2 + 8*r*X3, X2 - 2*(X1 - X3)];
        BB_1 := [[X + 8*r*Z, 2*X + Z],
            [Y^2 - 2*r*X*Z - 8*r*Y*Z + (256*r^3 - 32*r^2 + r)*Z^2,
            (-16*r + 1)*X^2 + 2*Y^2 + (64*r^2 - 8*r)*X*Z - Y*Z + (64*r^2 - 4*r)*Z^2]];
        BB_2 := [[X + 2*Y, -4*X - (16*r + 1)*Z],
            [Y^2 - r*Z^2, X^2 - 2*X*Y + 4*r*X*Z + (-8*r - 1)*Y*Z]];
        BB_E_C := [ SymMu4(S1,S2) : S1 in BB_1, S2 in BB_2 ];
    end if;
    C`WeierstrassMorphism := map< C->E | BB_C_E, BB_E_C >;
    // Install the addition morphism
    CxC := ProductScheme(C,C);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CxC);
    BB := [
        [
        (X1*Y3 + X3*Y1)*(X1*Y3 - X3*Y1),
        -X0*X3*Y1*Y2 + X1*X2*Y0*Y3,
        (X2*Y0 + X0*Y2)*(X2*Y0 - X0*Y2),
        -X0*X1*Y2*Y3 + X2*X3*Y0*Y1
        ],
        [
        (X0*Y0 + r*X2*Y2)*(X0*Y0 - r*X2*Y2),
        X0*X1*Y0*Y1 - r*X2*X3*Y2*Y3,
        (X1*Y1 + X3*Y3)*(X1*Y1 - X3*Y3),
        X0*X3*Y0*Y3 - r*X1*X2*Y1*Y2
        ],
        [
        X0*X1*Y0*Y3 + r*X2*X3*Y1*Y2,
        r*X0*X2*Y2^2 + X1^2*Y1*Y3,
        X0*X3*Y2*Y3 + X1*X2*Y0*Y1,
        X1*X3*Y3^2 - r*X2^2*Y0*Y2
        ],
        [
        X0*X3*Y0*Y1 + r*X1*X2*Y2*Y3,
        X1*X3*Y1^2 + r*X2^2*Y0*Y2,
        X0*X1*Y1*Y2 + X2*X3*Y0*Y3,
        -r*X0*X2*Y2^2 + X3^2*Y1*Y3
        ]
        ];
    C`AdditionMorphism := map< CxC->C | BB >;
    return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Semisplit mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Semisplit_Mu4_NormalForm(c::RngElt) -> Crv
    {}
    K := Parent(c);
    if Type(K) eq RngInt then K := RationalField(); c := K!c; end if;
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    require IsUnit(c) and c ne 4 and c ne -4:
        "Argument 2 must be a unit and not 4 or -4.";
    return EllipticCurve_Semisplit_Mu4_NormalForm(PP,c);
end intrinsic;

intrinsic EllipticCurve_Semisplit_Mu4_NormalForm(PP::Prj,c::RngElt) -> Crv
    {An elliptic curve in semisplit mu_4 normal form X0^2 - X2^2 = X1 X3,
    X1^2 - X3^2 = c*X0 X2, with identity O = (1:1:0:1)}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(c) and c ne 4 and c ne -4:
        "Argument 2 must be a unit and not 4 or -4.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    C := Curve(PP,[X0^2-X2^2-X1*X3,X1^2-X3^2-c*X0*X2]);
    C`EllipticModelType := "Semisplit mu_4 normal form";
    C`EllipticModelInvariants := [c];
    C`IdentityElement := [1,1,0,1];
    C`EmbeddingClass := [1,-1,0,-1];
    C`InverseMorphism := map< C->C | [X0,X3,-X2,X1] >;
    C`KummerMorphism := map< C->Curve(ProjectiveSpace(K,1)) | [[X0,X1+X3],[X1-X3,c*X2]] >;
    if Characteristic(K) eq 2 then
        E := EllipticCurve([1,0,0,0,1/c^2]);
        P2<X,Y,Z> := AmbientSpace(E);
        C`WeierstrassMorphism := map< C->E |
            [ X1 + X3, X0 + X1, c*X2 ],
            [ X^2, Y*Z + X^2, Z^2/c, (X + Y)*Z + X^2 ] >;
    else
        E := EllipticCurve([1,4/c^2,0,-4/c^2,-(c^2 + 16)/c^4]);
        P2<X,Y,Z> := AmbientSpace(E);
        A := [ X + 8/c^2*Z, 2*X + Z ];
        B := [ X + 2*Y, -4*X - (1 + 16/c^2)*Z ];
        BB := [ A[1]*B[1], (A[1]*B[2] + A[2]*B[1])/2, 1/c*A[2]*B[2], (A[2]*B[1] - A[1]*B[2])/2 ];
        C`WeierstrassMorphism := map< C->E | [
            -(X1 - X3) + 8/c*X2,
            X0 + X1 - 8/c^2*(2*X0 + X1 + X3) - 4/c*X2,
            2*(X1 - X3) - c*X2
            ], BB >;
    end if;
    // Install the addition morphism
    CxC := ProductScheme(C,C);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CxC);
    BB := [
        [
        X0^2*Y0^2 - X2^2*Y2^2,
        X0*X1*Y0*Y1 - X2*X3*Y2*Y3,
        1/c*(X1^2*Y1^2 - X3^2*Y3^2),
        X0*X3*Y0*Y3 - X1*X2*Y1*Y2
        ],
        [
        X0*X1*Y0*Y3 + X2*X3*Y1*Y2,
        c*X0*X2*Y2^2 + X1^2*Y1*Y3,
        X0*X3*Y2*Y3 + X1*X2*Y0*Y1,
        X1*X3*Y3^2 - c*X2^2*Y0*Y2
        ],
        [
        1/c*(X1^2*Y3^2 - X3^2*Y1^2),
        -X0*X3*Y1*Y2 + X1*X2*Y0*Y3,
        X2^2*Y0^2 - X0^2*Y2^2,
        -X0*X1*Y2*Y3 + X2*X3*Y0*Y1
        ],
        [
        X0*X3*Y0*Y1 + X1*X2*Y2*Y3,
        X1*X3*Y1^2 + c*X2^2*Y0*Y2,
        X0*X1*Y1*Y2 + X2*X3*Y0*Y3,
        -c*X0*X2*Y2^2 + X3^2*Y1*Y3
        ]
        ];
    C`AdditionMorphism := map< CxC->C | BB >;
    return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Split mu_4-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Split_Mu4_NormalForm(c::RngElt) -> Crv
    {}
    K := Parent(c);
    if Type(K) eq RngInt then K := RationalField(); c := K!c; end if;
    require IsUnit(c) and c^4 notin {K|4,-4}:
        "Argument 2 must be a unit not satisfying c^4 = 4 or -4.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Split_Mu4_NormalForm(PP,c);
end intrinsic;

intrinsic EllipticCurve_Split_Mu4_NormalForm(PP::Prj,c::RngElt) -> Crv
    {An elliptic curve in split mu_4-normal form: X_0^2 - X_2^2 = c^2 X_1 X_3,
    X_1^2 - X_3^2 = c^2 X_0 X_2 with identity (c:1:0:1).}
    K := BaseRing(PP);
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must coerce into the base ring of argument 1.";
    require IsUnit(c) and c^4 notin {K|4,-4}:
        "Argument 2 must be a unit not satisfying c^4 = 4 or -4.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    C := Curve(PP,[ X0^2 - X2^2 - c^2*X1*X3, X1^2 - X3^2 - c^2*X0*X2 ]);
    C`IdentityElement := [c,1,0,1];
    C`EmbeddingClass := [c,-1,0,-1];
    C`InverseMorphism := map< C->C | [ X0,X3,-X2,X1 ], [ X0,X3,-X2,X1 ] >;
    C`KummerMorphism := map< C->Curve(ProjectiveSpace(K,1)) | [[c*X0,X1+X3],[X1-X3,c*X2]] >;
    // 2-torsion points:
    //T1 := C![ c,-1, 0,-1 ];
    //T2 := C![ 0,-1,-c, 1 ];
    //T3 := C![ 0, 1,-c,-1 ];
    // 4-torsion elements:
    //P0 := C![ 1, c, 1, 0 ];
    //P1 := C![ 1,-c, 1, 0 ];
    //P2 := C![ 1, 0,-1, c ];
    //
    c1 := c^4;
    P2<X,Y,Z> := ProjectiveSpace(K,2);
    E := P2!!EllipticCurve([1,4/c1^2,0,-4/c1^2,-(c1^2+16)/c1^4]);
    if Characteristic(K) eq 2 then
        iso_C_E := map< C->E | [
            [ c*(X1 + X3), X0 + c*X1, c^4*X2 ],
            [ X0*(X0 + c*X3), X0^2 + 1/c^3*X1*X2 + 1/c^3*X2*X3, c*(X0 + c*X3)*(X1 + X3) ]
            ],
            [
            [ c*X^2, X^2 + Y*Z, 1/c^3*Z^2, X^2 + X*Z + Y*Z ],
            [ c*(c^8*(X + Y)*Y + Z^2), c^8*Y^2 + Z^2, c^5*X*Z, c^8*(X + Y)^2 + Z^2 ]
            ] >;
    else
        iso_C_E := map< C->E |
            [
            c*(X1 - X3) - 8/c^4*X2,
            (-c^8 + 16)/c^8*X0 + 4/c^4*X2 + c*(-c^8 + 8)/c^8*X1 + 8*c/c^8*X3,
            c^4*X2 - 2*c*(X1 - X3)
            ],
            [
            [
            c*(c^8*(c^8 - 8)*X^2 - 2*c^16*Y^2 + 8*c^8*X*Z + 16*c^8*Y*Z - 2*(c^8 - 16)*Z^2),
            c^8*(-(c^8 - 8)*X^2 + 2*c^8*(X - Y)*Y - 16*X*Z + (c^8 + 16)*Y*Z - 2*Z^2) - 96*Z^2,
            c*(-4*c^12*X^2 + 8*c^12*X*Y - 4*c^4*(c^8 + 8)*X*Z + 4*c^12*Y*Z - c^4*(c^8 + 16)*Z^2),
            c^8*((c^8 + 8)*X^2 - 2*c^8*(X + Y)*Y + (c^8 + 16)*X*Z + (c^8 - 16)*Y*Z + 6*Z^2) + 32*Z^2
            ],
            [
            c*((c^20 - 8*c^12)*X*Y + c^20*Y^2 - 32*c^4*X*Z - 64*c^4*Y*Z + (c^12 - 16*c^4)*Z^2),
            -8*c^12*X*Y + c^20*Y^2 + (-4*c^12 + 96*c^4)*X*Z - 12*c^12*Y*Z + (-c^16 + 32*c^8 + 256)/c^4*Z^2,
            c*((-2*c^16 + 32*c^8)*X^2 - 4*c^16*X*Y + (-c^16 + 24*c^8 + 128)*X*Z - 2*c^16*Y*Z + 4*(c^8 + 16)*Z^2),
            c^12*((c^8 - 16)*X^2 + 2*(c^8 - 4)*X*Y + c^8*Y^2 + 4*Y*Z - Z^2) - 16*(6*c^8*X + 16*Z)*Z/c^4
            ]
            ] >;
    end if;
    C`WeierstrassMorphism := iso_C_E;
    C`EllipticModelType := "Split mu_4 normal form";
    C`EllipticModelInvariants := [c];
    CxC := ProductScheme(C,C);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CxC);
    C`AdditionMorphism := map< CxC->C | [
        [
        X3^2*Y1^2 - X1^2*Y3^2,
        c*(X0*X3*Y1*Y2 - X1*X2*Y0*Y3),
        -X2^2*Y0^2 + X0^2*Y2^2,
        c*(X0*X1*Y2*Y3 - X2*X3*Y0*Y1)
        ],
        [
        X0^2*Y0^2 - X2^2*Y2^2,
        c*(X0*X1*Y0*Y1 - X2*X3*Y2*Y3),
        X1^2*Y1^2 - X3^2*Y3^2,
        c*(X0*X3*Y0*Y3 - X1*X2*Y1*Y2)
        ],
        [
        X2*X3*Y1*Y2 + X0*X1*Y0*Y3,
        c*(X0*X2*Y2^2 + X1^2*Y1*Y3),
        X1*X2*Y0*Y1 + X0*X3*Y2*Y3,
        c*(X1*X3*Y3^2 - X2^2*Y0*Y2)
        ],
        [
        X0*X3*Y0*Y1 + X1*X2*Y2*Y3,
        c*(X1*X3*Y1^2 + X2^2*Y0*Y2),
        X0*X1*Y1*Y2 + X2*X3*Y0*Y3,
        c*(X3^2*Y1*Y3 - X0*X2*Y2^2)
        ]
        ] >;
    return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Twisted mu_4-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Mu4_NormalForm(r::RngElt) -> Crv
    {}
    return EllipticCurve_Twisted_Mu4_NormalForm(r,-1);
end intrinsic;

intrinsic EllipticCurve_Twisted_Mu4_NormalForm(r::RngElt,a::RngElt) -> Crv
    {}
    K := Parent(r);
    if Type(K) eq RngInt then K := RationalField(); r := K!r; end if;
    bool, a := IsCoercible(K,a);
    require bool: "Argument 2 must be coercible to the parent of argument 1.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Twisted_Mu4_NormalForm(PP,r,a);
end intrinsic;

intrinsic EllipticCurve_Twisted_Mu4_NormalForm(PP::Prj,r::RngElt,a::RngElt) -> Crv
    {An elliptic curve in twisted mu_4 normal form defined by
    X0^2 - D r X2^2 = X1 X3 - a (X1 - X3)^2, X1^2 - X3^2 = X0 X2,
    where D = 4a + 1, with identity O = (1:1:0:1). This is a twist
    by the Artin-Schreier extension k[x]/(x^2 - x - a) [default a = -1],
    of the mu_4 normal form with parameter r (corresponding to twist
    by a = 0).}
    require Dimension(PP) eq 3 :
        "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, r := IsCoercible(K,r);
    require bool: "Argument 2 must be coercible to the base ring of argument 1.";
    bool, a := IsCoercible(K,a); D := 4*a + 1;
    require bool: "Argument 3 must be coercible to the base ring of argument 1.";
    if a eq 0 then
        // No twist so return the untwisted type:
        return EllipticCurve_Mu4_NormalForm(PP,r);
    end if;
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    CT := Curve(PP,[ X0^2 - D*r*X2^2 - X1*X3 + a*(X1 - X3)^2, X1^2 - X3^2 - X0*X2 ]);
    CT`IdentityElement := [1,1,0,1];
    CT`EmbeddingClass := [1,-1,0,-1];
    CT`InverseMorphism := map< CT->CT | [X0,X3,-X2,X1], [X0,X3,-X2,X1] >;
    if Characteristic(K) eq 2 then
        ET := EllipticCurve([1,a,0,0,r]);
        P2<X,Y,Z> := AmbientSpace(ET);
        CT`WeierstrassMorphism := map< CT->ET |
            [ X1 + X3, X0 + X1, X2 ],
            [ X^2, Y*Z + X^2, Z^2, (X + Y)*Z + X^2 ] >;
    else
        WT := EllipticCurve([1,a-8*r*D,0,D^2*2*r*(8*r-3),D^3*r*(4*r-1)]);
        P2<X,Y,Z> := AmbientSpace(WT);
        /*
        P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
        ET := Curve(P1xP1, 4*U0^2*V0^2 - U1^2*V0^2 + D*U0^2*V1^2 - 4*D*r*U1^2*V1^2);
        iso_WT_ET := map< WT->ET | [X + 4*D*r*Z, 2*X - D*(8*r - 1)*Z, X + 2*Y, 4*X + D*Z] >;
        iso_ET_CT := map< ET->CT | [2*U0*V0, U1*V0 + U0*V1, 2*U1*V1, U1*V0 - U0*V1] >;
        */
        U0, U1 := Explode([X + 4*D*r*Z, 2*X + D*(1 - 8*r)*Z]);
        V0, V1 := Explode([X + 2*Y, 4*X + D*Z]);
        CT`WeierstrassMorphism := map< CT->WT | [
            D*((1 - 8*r)*(X1 - X3) - 4*r*X2),
            D*((1 - 16*r)*X0 - 4*r*X1 + 2*r*X2 + (1 - 12*r)*X3),
            X2 - 2*(X1 - X3) ],
            [2*U0*V0, U1*V0 + U0*V1, 2*U1*V1, U1*V0 - U0*V1] >;
    end if;
    CT`EllipticModelType := "Twisted mu_4 normal form";
    CT`EllipticModelInvariants := [r,a];
    CT`KummerMorphism := map< CT->Curve(ProjectiveSpace(K,1)) | [[X0,X1+X3],[X1-X3,X2]] >;
    CTxCT := ProductScheme(CT,CT);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CTxCT);
    // See twisted split mu_4 normal form or (untwisted) semisplit mu_4 normal form for
    // a basis of all addition laws. The following system is, however, complete.
    U00, U11, U22, U33 := Explode([ X0*Y0, X1*Y1, X2*Y2, X3*Y3 ]);
    U02, U13, U20, U31 := Explode([ X0*Y2, X1*Y3, X2*Y0, X3*Y1 ]);
    V13 := (X1 + X3)*(Y1 + Y3);
    W13 := (X1 - X3)*(Y1 - Y3);
    if Characteristic(K) eq 2 then
        mu_CT := map< CTxCT->CT | [
            [
            (U00 + r*U22)^2, (U00*U11 + r*U22*U33) + a*(U00 + r*U22)*W13,
            (U11 + U33)^2, (U00*U33 + r*U22*U11) + a*(U00 + r*U22)*W13
            ],
            [
            (U13 + U31)^2, (U20*U13 + U02*U31) + a*(U02 + U20)*W13,
            (U20 + U02)^2, (U20*U31 + U02*U13) + a*(U02 + U20)*W13 ]
            ] >;
    else
        BB_1 := [[U00 + D*r*U22, U11 + U33 + 2*a*W13], [U13 - U31, U20 - U02]];
        BB_2 := [[U00 - D*r*U22, U11 - U33], [U13 + U31 - 2*a*W13, U02 + U20]];
        SymMu4 := func< A, B | [2*A[1]*B[1], A[2]*B[1]+A[1]*B[2], 2*A[2]*B[2], A[2]*B[1]-A[1]*B[2]] >;
        mu_CT := map< CTxCT->CT | [ SymMu4(S1,S2) : S1 in BB_1, S2 in BB_2 ] >;
    end if;
    CT`AdditionMorphism := mu_CT;
    return CT;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Twisted semisplit mu_4-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(s::RngElt) -> Crv
    {}
    return EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(s,-1);
end intrinsic;

intrinsic EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(s::RngElt,a::RngElt) -> Crv
    {}
    bool, K, s, a := HasCommonField(s,a);
    require bool: "Arguments must be coercible to the a common base ring.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(PP,s,a);
end intrinsic;

intrinsic EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(PP::Prj,s::RngElt,a::RngElt) -> Crv
    {The twist by the extension k[x]/(x^2 - x - a) [default a = -1]) of
    the elliptic curve in semisplit mu_4-normal form: X0^2 + X2^2 = X1 X3,
    X1^2 + X3^2 + s X0 X2.}
    require Dimension(PP) eq 3 :
        "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, s := IsCoercible(K,s);
    require bool: "Argument 2 must be coercible to the base ring of argument 1.";
    bool, a := IsCoercible(K,a); D := 4*a + 1;
    require bool: "Argument 3 must be coercible to the base ring of argument 1.";
    if a eq 0 then
        // No twist so return the untwisted type:
        return EllipticCurve_Semisplit_Mu4_NormalForm(PP,s);
    end if;
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    CT := Curve(PP,[ X0^2 - D*X2^2 - X1*X3 + a*(X1 - X3)^2, X1^2 - X3^2 - s*X0*X2 ]);
    CT`IdentityElement := [1,1,0,1];
    CT`EmbeddingClass := [1,-1,0,-1];
    CT`InverseMorphism := map< CT->CT | [X0,X3,-X2,X1], [X0,X3,-X2,X1] >;
    if Characteristic(K) eq 2 then
        ET := EllipticCurve([1,a,0,0,1/s^2]);
        P2<X,Y,Z> := AmbientSpace(ET);
        CT`WeierstrassMorphism := map< CT->ET |
            [ X1 + X3, X0 + X1, s*X2 ],
            [ X^2, Y*Z + X^2, Z^2/s, (X + Y)*Z + X^2 ] >;
    else
        CX := Curve(PP,[ D*X0^2 - X2^2 - X1*X3 - a*(X1 + X3)^2, X1^2 - X3^2 - s*X0*X2 ]);
        iso_CX_CT := map< CX->CT |
            [ D*X0, X1 + 2*a*(X1 + X3), X2, X3 + 2*a*(X1 + X3) ],
            [ X0, X1 + 2*a*(X1 - X3), D*X2, X3 - 2*a*(X1 - X3) ] >;
        iso_CT_CX := Inverse(iso_CX_CT);
        ET := EllipticCurve([1,a+4*D/s^2,0,-4*D^2/s^2,-(s^2 + 16)*D^3/s^4]);
        P2<X,Y,Z> := AmbientSpace(ET);
        U0,U1 := Explode([X + 8*D/s^2*Z, 2*X + D*Z]);
        V0,V1 := Explode([X + 2*Y, -D*(4*X + D*(1 + 16/s^2)*Z)]);
        CT`WeierstrassMorphism := iso_CT_CX * map< CX->ET | [
            -(X1 - X3) + 8/s*X2,
            D*(1 - 16/s^2)*X0 + X1 - 8*D/s^2*(X1 + X3) + 2*a*(X1 + X3) - 4/s*X2,
            (2*(X1 - X3) - s*X2)/D],
            [ 2*U0*V0, U0*V1 + U1*V0, 2/s*U1*V1, U1*V0 - U0*V1 ] >;
    end if;
    CT`EllipticModelType := "Twisted semisplit mu_4 normal form";
    CT`EllipticModelInvariants := [s,a];
    CT`KummerMorphism := map< CT->Curve(ProjectiveSpace(K,1)) | [[X0,X1+X3],[X1-X3,s*X2]] >;
    CTxCT := ProductScheme(CT,CT);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CTxCT);
    // See twisted split mu_4 normal form or (untwisted) semisplit mu_4 normal form for
    // a basis of all addition laws. The following system is, however, complete.
    U00, U11, U22, U33 := Explode([ X0*Y0, X1*Y1, X2*Y2, X3*Y3 ]);
    U02, U13, U20, U31 := Explode([ X0*Y2, X1*Y3, X2*Y0, X3*Y1 ]);
    V13 := (X1 + X3)*(Y1 + Y3);
    W13 := (X1 - X3)*(Y1 - Y3);
    if Characteristic(K) eq 2 then
        mu_CT := map< CTxCT->CT | [
            [
            (U00 + U22)^2,
            (U00*U11 + U22*U33) + a*(U00 + U22)*W13,
            1/s*(U11 + U33)^2,
            (U00*U33 + U22*U11) + a*(U00 + U22)*W13
            ],
            [
            1/s*(U13 + U31)^2,
            (U20*U13 + U02*U31) + a*(U02 + U20)*W13,
            (U20 + U02)^2,
            (U20*U31 + U02*U13) + a*(U02 + U20)*W13
            ]
            ] >;
    else
        BB_1 := [[U00 + D*U22, 1/s*(U11 + U33 + 2*a*W13)], [U13 - U31, U20 - U02]];
        BB_2 := [[U00 - D*U22, 1/s*(U11 - U33)], [U13 + U31 - 2*a*W13, U02 + U20]];
        SymMu4 := func< A, B | [2/s*A[1]*B[1], (A[2]*B[1]+A[1]*B[2]), 2*A[2]*B[2], (A[2]*B[1]-A[1]*B[2])] >;
        mu_CT := map< CTxCT->CT | [ SymMu4(S1,S2) : S1 in BB_1, S2 in BB_2 ] >;
    end if;
    CT`AdditionMorphism := mu_CT;
    return CT;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Twisted split mu_4-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Split_Mu4_NormalForm(c::RngElt) -> Crv
    {}
    return EllipticCurve_Twisted_Split_Mu4_NormalForm(c,-1);
end intrinsic;

intrinsic EllipticCurve_Twisted_Split_Mu4_NormalForm(c::RngElt,a::RngElt) -> Crv
    {The twist by the extension k[x]/(x^2 - x - a) [default a = -1]) of
    the elliptic curve in split mu_4-normal form: X0^2 + X2^2 = c^2 X1 X3,
    X1^2 + X3^2 + c^2 X0 X2.}
    K := Parent(c);
    if Type(K) eq RngInt then K := RationalField(); c := K!c; end if;
    bool, a := IsCoercible(K,a);
    require bool: "Argument 2 must be coercible to the parent of argument 1.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Twisted_Split_Mu4_NormalForm(PP,c,a);
end intrinsic;

intrinsic EllipticCurve_Twisted_Split_Mu4_NormalForm(PP::Prj,c::RngElt) -> Crv
    {}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    bool, c := IsCoercible(BaseRing(PP),c);
    require bool: "Argument 2 must be coercible to the base ring of argument 1.";
    return EllipticCurve_Twisted_Split_Mu4_NormalForm(PP,c,-1);
end intrinsic;

intrinsic EllipticCurve_Twisted_Split_Mu4_NormalForm(PP::Prj,c::RngElt,a::RngElt) -> Crv
    {The twist by the extension k[x]/(x^2 - x - a) [default a = -1] of the elliptic
    curve in split mu_4-normal form X0^2 - X2^2 = c^2 X1 X3, X1^2 - X3^2 + c^2 X0 X2
    in PP (= PP^3). The twist is valid in any characteristic, is an Artin-Schreier
    twist in characteristic 2, and is a twist by D = 4a + 1 (i.e. by the
    extension k[\delta]/(\delta^2-D)) in any other characteristic.}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible to the base ring of argument 1.";
    bool, a := IsCoercible(K,a);
    require bool: "Argument 3 must be coercible to the base ring of argument 1.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    D := 1 + 4*a; // Here we twist by k[x]/(x^2-x-a):
    CT := Curve(PP,[ X0^2 - D*X2^2 - c^2*(X1*X3 - a*(X1 - X3)^2), X1^2 - X3^2 - c^2*X0*X2 ]);
    CT`IdentityElement := [c,1,0,1];
    CT`EmbeddingClass := [c,-1,0,-1];
    CT`InverseMorphism := map< CT->CT | [X0,X3,-X2,X1], [X0,X3,-X2,X1] >;
    E1 := EllipticCurve([1,a+4*D/c^8,0,-4*D^2/c^8,-(c^8 + 16)*D^3/c^16]);
    CT`EllipticModelType := "Twisted split mu_4 normal form";
    CT`EllipticModelInvariants := [c,a];
    // This gives a morphism to Weierstrass form but results
    // in a curve with larger discriminant than necessary:
    C2, iso_CT_C2 := EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(CT);
    WT, iso_C2_WT := WeierstrassModel(C2);
    CT`WeierstrassMorphism := iso_CT_C2 * iso_C2_WT;
    CT`KummerMorphism := map< CT->Curve(ProjectiveSpace(K,1)) | [[c*X0,X1+X3],[X1-X3,c*X2]] >;
    CTxCT := ProductScheme(CT,CT);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CTxCT);
    U00, U11, U22, U33 := Explode([ X0*Y0, X1*Y1, X2*Y2, X3*Y3 ]);
    U02, U13, U20, U31 := Explode([ X0*Y2, X1*Y3, X2*Y0, X3*Y1 ]);
    V13 := (X1 + X3)*(Y1 + Y3);
    W13 := (X1 - X3)*(Y1 - Y3);
    if Characteristic(K) eq 2 and a eq 1 then
        BB_CT := [
            // Addition laws exchanged by 2-torsion point S -- (P,Q) == (P+S,Q)+S
            [ // 9M + 2S + 3m
            (X1*Y3 + X3*Y1)^2, // 2M + 1S
            c*((X1 + X3)*(Y1 + Y3)*(X0*Y2 + X2*Y0) + X0*X3*Y1*Y2 + X1*X2*Y0*Y3), // 4M + 2m
            (X0*Y2 + X2*Y0)^2, // 2M + 1S
            c*((X1 + X3)*(Y1 + Y3)*(X0*Y2 + X2*Y0) + X0*X1*Y2*Y3 + X2*X3*Y0*Y1)  // 1M + 1m
            ],
            [ // 9M + 2S + 3m
            (X0*Y0 + X2*Y2)^2, // 2M + 1S
            c*((X1 + X3)*(Y1 + Y3)*(X0*Y0 + X2*Y2) + X0*Y0*X1*Y1 + X2*Y2*X3*Y3), // 4M + 2m
            (X1*Y1 + X3*Y3)^2, // 2M + 1S
            c*((X1 + X3)*(Y1 + Y3)*(X0*Y0 + X2*Y2) + X0*Y0*X3*Y3 + X1*Y1*X2*Y2)  // 1M + 1m
            ],
            [ // Eigenspace for 2-torsion point S -- (P,Q) == (P+S,Q)+S
            (X0*Y0 + X2*Y2)*(X1*Y3 + X3*Y1),
            c*((X1*Y3 + X3*Y1)*(X1*Y3 + X3*Y1 + X3*Y3) + X2*Y2*(X2*Y0 + X0*Y2)),
            (X1*Y1 + X3*Y3)*(X0*Y2 + X2*Y0),
            c*((X1*Y3 + X3*Y1)*(X1*Y1 + X1*Y3 + X3*Y1) + X2*Y2*(X2*Y0 + X0*Y2))
            ],
            [
            c*((X0*Y0 + X2*Y2)*(X1 + X3)*(Y1 + Y3) + X0*Y0*X3*Y1 + X1*X2*Y2*Y3),
            ((X1 + X3)*(Y0 + Y2) + X0*Y1 + X2*Y3)^2,
            c*(X0*Y2*(X3*Y1 + X1*Y3 + X3*Y3) + X2*Y0*(X1*Y1 + X1*Y3 + X3*Y1)),
            ((X0 + X2)*(Y1 + Y3) + X1*Y2 + X3*Y0)^2
            ]
            ];
        mu_CT := map< CTxCT->CT | BB_CT >;
    elif Characteristic(K) eq 2 then
        BB_CT := [
            [ // 9M + 2S + 3m
            (X1*Y3 + X3*Y1)^2, // 2M + 1S
            c*(a*(X1 + X3)*(Y1 + Y3)*(X0*Y2 + X2*Y0) + X0*X3*Y1*Y2 + X1*X2*Y0*Y3), // 4M + 2m
            (X0*Y2 + X2*Y0)^2, // 2M + 1S
            c*(a*(X1 + X3)*(Y1 + Y3)*(X0*Y2 + X2*Y0) + X0*X1*Y2*Y3 + X2*X3*Y0*Y1)  // 1M + 1m
            ],
            [ // 9M + 2S + 3m
            (X0*Y0 + X2*Y2)^2, // 2M + 1S
            c*(a*(X1 + X3)*(Y1 + Y3)*(X0*Y0 + X2*Y2) + X0*X1*Y0*Y1 + X2*X3*Y2*Y3), // 4M + 2m
            (X1*Y1 + X3*Y3)^2, // 2M + 1S
            c*(a*(X1 + X3)*(Y1 + Y3)*(X0*Y0 + X2*Y2) + X0*X3*Y0*Y3 + X1*X2*Y1*Y2)  // 1M + 1m
            ],
            // The latter two are equivalent modulo the defining ideal of CT x CT.
            [
            (X0*Y0 + X2*Y2)*(X1*Y3 + X3*Y1), // AC: A+B = (X0+X2)*(Y0+Y2)
            c*(a*(X1 + X3)*(Y1 + Y3)*(X1*Y3 + X3*Y1) + (X0*Y2 + X2*Y0)*X2*Y2 + (X1*Y3 + X3*Y1)*X1*Y1),
            (X0*Y2 + X2*Y0)*(X1*Y1 + X3*Y3), // BD: C+D = (X1+X3)*(Y1+Y3) -- 6M instead of 4M + 2S
            c*(a*(X1 + X3)*(Y1 + Y3)*(X1*Y3 + X3*Y1) + (X0*Y2 + X2*Y0)*X2*Y2 + (X3*Y1 + X1*Y3)*X3*Y3)
            ],
            [
            (X0*Y0 + X2*Y2)*(X1*Y3 + X3*Y1),
            c*(a*(X1*Y1 + X3*Y3)*(X1*Y3 + X3*Y1) + (X0*Y1 + X1*Y0 + X2*Y3 + X3*Y2)^2/c^2),
            (X0*Y2 + X2*Y0)*(X1*Y1 + X3*Y3),
            c*(a*(X1*Y1 + X3*Y3)*(X1*Y3 + X3*Y1) + (X0*Y3 + X3*Y0 + X1*Y2 + X2*Y1)^2/c^2)
            ]
            // There is a fourth basis element but I haven't found a simple enough expression.
            ];
        mu_CT := map< CTxCT->CT | BB_CT >;
    else
        BB_1 := [[U00 + D*U22, U11 + U33 + 2*a*W13],[U13 - U31, U20 - U02]];
        BB_2 := [[U00 - D*U22, U11 - U33],[U13 + U31 - 2*a*W13, U02 + U20]];
        SymMu4 := func< A, B | [2*A[1]*B[1], c*(A[2]*B[1]+A[1]*B[2]), 2*A[2]*B[2], c*(A[2]*B[1]-A[1]*B[2])] >;
        mu_CT := map< CTxCT->CT | [ SymMu4(S1,S2) : S1 in BB_1, S2 in BB_2 ] >;
    end if;
    CT`AdditionMorphism := mu_CT;
    return CT;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Jacobi models
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Jacobi_NormalForm(PP::Prj,abc::[RngElt]) -> Crv
    {Given abc = [a,b,c], returns the elliptic curve in Jacobi model:
    aX0^2 + X1^2 = X2^2, bX0^2 + X2^2 = X3^2, cX0^2 + X3^2 = X1^2,
    where a + b + c = 0, and identity (0:1:1:1); if c is not given
    then it is computed.}

    require Dimension(PP) eq 3 :
        "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, abc := CanChangeUniverse(abc,K);
    require bool: "Elements of argument 2 must be coercible into the base ring of argument 1.";
    if #abc eq 2 then
        a,b := Explode(abc); c := -(a+b);
    elif #abc eq 3 then
        a,b,c := Explode(abc);
        require a+b+c eq 0 :
            "Argument 2 must consist of three elements whose sum is zero.";
    else
        require false: "Argument must be a sequence of two or three elements.";
    end if;
    require a ne 0 and b ne 0 and c ne 0: "Argument must consist of nonzero elements.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    J := Curve(PP,[ a*X0^2 + X1^2 - X2^2, b*X0^2 + X2^2 - X3^2, c*X0^2 + X3^2 - X1^2 ]);
    J`EllipticModelType := "Jacobi";
    J`EllipticModelInvariants := [a,b,c];
    J`IdentityElement := [0,1,1,1];
    J`EmbeddingClass := [0,1,1,1];
    J`InverseMorphism := map< J->J | [X0,-X1,-X2,-X3] >;
    //
    E := EllipticCurve([0,-a + b,0,-a*b,0]);
    P2<X,Y,Z> := AmbientSpace(E);
    J`WeierstrassMorphism := map< J->E |
        [ a*b*(X1 - X3), a*(a + b)*b*X0, b*X1 + c*X2 + a*X3 ],
        [
        [-2*Y*Z, X^2 - 2*a*X*Z - a*b*Z^2,X^2 + a*b*Z^2,X^2 + 2*b*X*Z - a*b*Z^2],
        [-2*X*Y, c*X^2 + Y^2, (a - b)*X^2 + Y^2 + 2*a*b*X*Z, -c*X^2 + Y^2 ]
        ] >;
    P2<U0,U1,U2> := ProjectiveSpace(K,2);
    K1 := Curve(P2,a*U0^2+b*U1^2+c*U2^2);
    J`KummerMorphism := map< J->K1 | [X3,X1,X2] >;
    // Install the addition morphism
    JxJ := ProductScheme(J,J);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(JxJ);
    BB := [
        [
        X0^2*Y1^2 - X1^2*Y0^2,
        X0*X1*Y2*Y3 - X2*X3*Y0*Y1,
        X0*X2*Y1*Y3 - X1*X3*Y0*Y2,
        X0*X3*Y1*Y2 - X1*X2*Y0*Y3
        ],
        [
        X0*X1*Y2*Y3 + X2*X3*Y0*Y1,
        a*c*X0^2*Y0^2 + X1^2*Y1^2,
        a*X0*X3*Y0*Y3 + X1*X2*Y1*Y2,
        -c*X0*X2*Y0*Y2 + X1*X3*Y1*Y3
        ],
        [
        X0*X2*Y1*Y3 + X1*X3*Y0*Y2,
        -a*X0*X3*Y0*Y3 + X1*X2*Y1*Y2,
        a*b*X0^2*Y0^2 + X2^2*Y2^2,
        b*X0*X1*Y0*Y1 + X2*X3*Y2*Y3
        ],
        [
        a*(X0*X3*Y1*Y2 + X1*X2*Y0*Y3),
        a*(c*X0*X2*Y0*Y2 + X1*X3*Y1*Y3),
        a*(-b*X0*X1*Y0*Y1 + X2*X3*Y2*Y3),
        -b*X1^2*Y1^2 - c*X2^2*Y2^2
        ]
        ];
    J`AdditionMorphism := map< JxJ->J | BB >;
    return J;
end intrinsic;

intrinsic EllipticCurve_Jacobi_NormalForm(abc::[RngElt]) -> Crv
    {Given abc = [a,b,c], returns the elliptic curve in Jacobi model:
    aX0^2 + X1^2 = X2^2, bX0^2 + X2^2 = X3^2, cX0^2 + X3^2 = X1^2,
    where a + b + c = 0, and identity (0:1:1:1); if c is not given
    then it is computed.}

    K := Universe(abc);
    if Type(K) eq RngInt then K := RationalField(); end if;
    if #abc eq 2 then
        a,b := Explode(abc); c := -(a+b);
    elif #abc eq 3 then
        a,b,c := Explode(abc);
        require a+b+c eq 0 :
            "Argument 2 must consist of three elements whose sum is zero.";
    else
        require false: "Argument must be a sequence of two or three elements.";
    end if;
    require a ne 0 and b ne 0 and c ne 0: "Argument must consist of nonzero elements.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Jacobi_NormalForm(PP,[K|a,b,c]);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic Curves in Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

/*
FF<c> := FunctionField(ZZ);
PP<X0,X1,X2,X3> := ProjectiveSpace(FF,3);
EE := Curve(PP,[X0^2-X1^2+X2^2-X3^2-c*X0*X2,X0*X2-X1*X3]);
OE := EE![ 1, 0, 0, 1];
TE := EE![ 1, 1, 0, 0];
SE := EE![ 0,-1, 1, 0];
RE := EE![ 0, 0,-1, 1];
E4, iso_EE_E4, e4 := EllipticCurve_C4_NormalForm(EE,[OE,TE,SE,RE]);
//
CC := EllipticCurve_Split_Mu4_NormalForm(PP,c);
OC := Identity(CC);
TC := CC![1,c,1,0];
SC := CC![0,-1,-c,1];
RC := -TC;
EC, iso_CC_EC, eC := EllipticCurve_C4_NormalForm(CC,[OC,TC,SC,RC]);
//iso_EC_CC := Inverse(iso_CC_EC);
*/

intrinsic EllipticCurve_C4_NormalForm(e::RngElt) -> Crv
    {}
    K := Parent(e);
    if Type(K) eq RngInt then K := RationalField(); e := K!e; end if;
    require IsUnit(e) and e ne 8 and e ne -8:
        "Argument must be a unit different from 8 and -8.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_C4_NormalForm(PP,e);
end intrinsic;

intrinsic EllipticCurve_C4_NormalForm(PP::Prj,e::RngElt) -> Crv
    {The elliptic curve in Z/4Z-normal form in PP (= PP^3), given by
    (X0 - X1 + X2 - X3)^2 - (e + 8)*X0*X2, X0*X2 - X1*X3, with identity (1:0:0:1).}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    K := BaseRing(PP);
    bool, e := IsCoercible(K,e);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(e) and e ne 8 and e ne -8:
        "Argument 2 must be a unit different from 8 and -8.";
    C := Curve(PP,[ (X0 - X1 + X2 - X3)^2 - (e + 8)*X0*X2, X0*X2 - X1*X3 ]);
    C`IdentityElement := [1,0,0,1];
    C`EmbeddingClass := [0,1,1,0];
    C`InverseMorphism := map< C->C | [X3,X2,X1,X0], [X3,X2,X1,X0] >;
    P1 := Curve(ProjectiveSpace(K,1));
    C`KummerMorphism := map< C->P1 | [[X0,X1],[X3,X2]] >;
    if Characteristic(K) eq 2 then
        E := EllipticCurve([1,0,0,1/e^2,0]);
        P2<X,Y,Z> := AmbientSpace(E);
        iso_C_E := map< C->E | [
            [ 1/e*(X1 + X2), 1/e*X1, X0 + X3 ],
            [ 1/e*X2*X3, 1/e^2*((X1+X2)*X2 + (X0 + X3)*X3), X3^2 ]
            ],
            [
            [ (X + 1/e*Z)^2, e*(X + Y)*Y, e*(X + Y)^2, X*(X + Z) + (Y + 1/e^2*Z)*Z ],
            [ X^3 + (X + Y)*Y*Z + 1/e^2*(X + Y)*Z^2, 1/e*X*Y*Z, 1/e*X*(X + Y)*Z, 1/e^2*(X + Y)*Z^2 ]
            ] >;
    else
        E := EllipticCurve([1,2/e,0,(e + 8)^2/e^4,0]);
        P2<X,Y,Z> := AmbientSpace(E);
        iso_C_E := map< C->E |
            [ (e + 8)/e^2*(X0 - X3), (e + 8)/e^3*(4*X0 + (e + 4)*X3), X1 - X2 ],
            [ X*((e + 4)*X + e*Y),
            (e + 8)/e*((e + 4)/e*X + Y)*Z,
            (e + 8)/e*(-4/e*X + Y)*Z,
            X*(-4*X + e*Y)
            ] >;
    end if;
    CxC := ProductScheme(C,C);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CxC);
    if Characteristic(K) eq 2 then
        BB_pi1 := [ [ X3*Y0 + X1*Y2, X0*Y1 + X2*Y3 ], [ X2*Y1 + X0*Y3, X1*Y0 + X3*Y2 ] ];
        BB_pi2 := [ [ X3*Y1 + X1*Y3, X0*Y2 + X2*Y0 ], [ X0*Y0 + X2*Y2, X1*Y1 + X3*Y3 ] ];
    else
        SX := X0 - X1 + X2 - X3;
        SY := Y0 - Y1 + Y2 - Y3;
        BB_pi1 := [
            [
            X1*Y2 + X3*Y0 + 2/(e+4)*(X0*Y3 + X1*Y2 + X2*Y1 + X3*Y0 + SX*SY),
            X0*Y1 + X2*Y3 + 2/(e+4)*(X0*Y1 + X1*Y0 + X2*Y3 + X3*Y2 + SX*SY)
            ],
            [
            X0*Y3 + X2*Y1 + 2/(e+4)*(X0*Y3 + X1*Y2 + X2*Y1 + X3*Y0 + SX*SY),
            X1*Y0 + X3*Y2 + 2/(e+4)*(X0*Y1 + X1*Y0 + X2*Y3 + X3*Y2 + SX*SY)
            ]
            ];
        // The simplest addition law projection does not reduce to the simplest in characteristic 2:
        /* [ X0*Y3 + X2*Y1 - X1*Y2 - X3*Y0, - X0*Y1 + X1*Y0 - X2*Y3 + X3*Y2 ] */
        BB_pi2 := [
            [
            X1*Y3 + X3*Y1 + 2/(e+4)*(X0*Y0 + X1*Y3 + X2*Y2 + X3*Y1 - SX*SY),
            X0*Y2 + X2*Y0 + 2/(e+4)*(X0*Y2 + X1*Y1 + X2*Y0 + X3*Y3 - SX*SY)
            ],
            [
            X0*Y0 + X2*Y2 + 2/(e+4)*(X0*Y0 + X3*Y1 + X2*Y2 + X1*Y3 - SX*SY),
            X1*Y1 + X3*Y3 + 2/(e+4)*(X0*Y2 + X1*Y1 + X2*Y0 + X3*Y3 - SX*SY)
            ]
            ];
        // The simplest addition law projection does not reduce to the simplest in characteristic 2:
        /* [ X0*Y0 + X2*Y2 - X1*Y3 - X3*Y1, - X0*Y2 + X1*Y1 - X2*Y0 + X3*Y3 ] */
    end if;
    C`EllipticModelType := "Z/4Z-normal form";
    C`EllipticModelInvariants := [e];
    P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
    C1 := Curve(P1xP1,(U0-U1)^2*(V0-V1)^2 - (e+8)*U0*U1*V0*V1);
    // Observed to be expensive to evaluate in a 'reasonable' example:
    mu_pixpi := map< CxC->C1 | [ S1 cat S2 : S1 in BB_pi1, S2 in BB_pi2 ] >;
    SkewSegre := map< C1->C | [U0*V0, U1*V0, U1*V1, U0*V1] >;
    C`AdditionMorphism := mu_pixpi * SkewSegre;
    C`WeierstrassMorphism := iso_C_E;
    return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in semisplit Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Semisplit_C4_NormalForm(c::RngElt) -> Crv
    {}
    K := Parent(c);
    if Type(K) eq RngInt then K := RationalField(); c := K!c; end if;
    require IsUnit(c) and c ne 4 and c ne -4:
        "Argument must be a unit different from 4 and -4.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    if Characteristic(K) eq 2 then
        return EllipticCurve_C4_NormalForm(PP,c);
    else
        return EllipticCurve_Semisplit_C4_NormalForm(PP,c);
    end if;
end intrinsic;

intrinsic EllipticCurve_Semisplit_C4_NormalForm(PP::Prj,c::RngElt) -> Crv
    {An elliptic curve in semisplit Z/4Z-normal form in PP (= PP^3), given by
    X0^2 - X1^2 + X2^2 - X3^2 = c X0 X2 = c X1 X3,
    with identity O = (1:0:0:1), 4-torsion point T = (1:1:0:0),
    and 2-torsion point S = (-1:0:0:1).}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    K := BaseRing(PP);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(c) and c ne 4 and c ne -4:
        "Argument 2 must be a unit different from 4 and -4.";
    if Characteristic(K) eq 2 then
        return EllipticCurve_C4_NormalForm(PP,c);
    end if;
    C := Curve(PP,[ X0^2 - X1^2 + X2^2 - X3^2 - c*X0*X2, X0*X2 - X1*X3 ]);
    C`EllipticModelType := "Semisplit Z/4Z-normal form";
    C`EllipticModelInvariants := [c];
    C`IdentityElement := [1,0,0,1];
    C`EmbeddingClass := [0,1,1,0];
    C`InverseMorphism := map< C->C | [X3,-X2,-X1,X0], [X3,-X2,-X1,X0] >;
    P1 := Curve(ProjectiveSpace(K,1));
    C`KummerMorphism := map< C->P1 | [[X0+X3,X1-X2],[2*(X1+X2)+c*X3,2*(X0-X3)-c*X2]] >;
    E := EllipticCurve([c,4,0,c^2,0]);
    P2<X,Y,Z> := AmbientSpace(E);
    BB_1 := [
        -c*(c*(X0 - X3) - 4*(X1 + X2)),
        c*(c^2*X0 - 2*c*(X1 + X2) - 8*(X0 + X3)),
        4*(X0 - X3) - c*(X1 + X2) ];
    BB_2 := [ [ X*(Y - 2*c*Z), -2*X^2 + c*Y*Z, -2*X^2 - c^2*X*Z - c*Y*Z, X*(c*X + Y + 2*c*Z)],
        [ Y*(Y - 2*c*Z), c*X^2 + 4*c*X*Z - 2*X*Y - c^2*Y*Z + c^3*Z^2,
        -c*X^2 - 4*c*X*Z - 2*X*Y - c^3*Z^2, Y*(c*X + Y + 2*c*Z) ] ];
    iso_C_E := map< C->E | BB_1, BB_2 >;
    C`WeierstrassMorphism := iso_C_E;
    CxC := ProductScheme(C,C);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(CxC);
    BB_1 := [ [ X0*Y3 + X2*Y1, X1*Y0 + X3*Y2 ], [ X1*Y2 + X3*Y0, X0*Y1 + X2*Y3 ] ];
    BB_2 := [ [ X0*Y0 - X2*Y2,-X1*Y1 + X3*Y3 ], [ X1*Y3 - X3*Y1,-X0*Y2 + X2*Y0 ] ];
    P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
    C1 := Curve(P1xP1,(U0^2-U1^2)*(V0^2-V1^2) - c*U0*U1*V0*V1);
    mu_pixpi := map< CxC->C1 | [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ] >;
    SkewSegre := map< C1->C | [U0*V0, U1*V0, U1*V1, U0*V1] >;
    C`AdditionMorphism := mu_pixpi * SkewSegre;
    return C;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Split Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Split_C4_NormalForm(u::RngElt) -> Crv
    {}
    K := Parent(u);
    if Type(K) eq RngInt then K := RationalField(); u := K!u; end if;
    require IsUnit(u): "Argument must be a unit.";
    require u ne 1: "Argument 2 must not be 1 or -1.";
    require u ne -1: "Argument 2 must not be 1 or -1.";
    require IsUnit(u^2+1): "Argument must not be a root of x^2+1.";
    require IsUnit(u^2+1): "Argument must not be a root of x^2+1.";
    require IsUnit(u^4+6*u^2+1): "Argument must not be a root of x^4+6*x^2+1.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Split_C4_NormalForm(PP,u);
end intrinsic;

intrinsic EllipticCurve_Split_C4_NormalForm(PP::Prj,u::RngElt) -> Crv
    {An elliptic curve in split Z/4Z-normal form, given by X0^2 + X2^2 = a*X1*X3,
    X1^2 + X3^2 = a*X0*X2, with identity (-1:-1:u:u), where a = -(u + 1/u).}
    K := BaseRing(PP);
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    bool, u := IsCoercible(K,u);
    require bool: "Argument 2 must define an element of the base ring of argument 1.";
    require IsUnit(u): "Argument must be a unit.";
    require u ne 1: "Argument 2 must not be 1 or -1.";
    require u ne -1: "Argument 2 must not be 1 or -1.";
    require IsUnit(u^2+1): "Argument must not be a root of x^2+1.";
    require IsUnit(u^4+6*u^2+1): "Argument must not be a root of x^4+6*x^2+1.";
    s := 1/(u-1); // u eq (s+1)/s;
    a := (u + 1/u); // a eq (2*(s^2 + s) + 1)/(s^2 + s);
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    //assert false;// Characteristic 2 only???
    E := Curve(PP,[ X0^2 + X2^2 + a*X1*X3, X1^2 + X3^2 + a*X0*X2 ]);
    P1 := Curve(ProjectiveSpace(K,1));
    E`IdentityElement := [-1,-1,u,u];
    E`EmbeddingClass := [u,u,-1,-1];
    E`EllipticModelType := "Split Z/4Z-normal form";
    E`EllipticModelInvariants := [u];
    E`InverseMorphism := map< E->E | [X1,X0,X3,X2] >;
    // Simple map, not compatible with other Z/4Z-normal forms:
    // E`KummerMorphism := map< E->P1 | [ [X0+X1,X2+X3], [ a*X0-(X2-X3), (X0-X1)+a*X3 ] ] >;
    // Compatible with semisplit mu_4-normal form:
    BB_K := [
        [ X0 - u*X2, a*(u*X1 - X3) ],
        [ X1 - u*X3, a*(u*X0 - X2) ]
        ];
    // Compatible with semisplit Z/4Z-normal form:
    BB_K := [
        [ (X0+X1) + u*(X2+X3), u*(X0+X1) + (X2+X3) ],
        [ a*(X0-u*X2) - 2*(u*X1-X3), 2*(X0-u*X2) - a*(u*X1-X3) ]
        ];
    E`KummerMorphism := map< E->P1 | BB_K >;
    E0 := EllipticCurve([ u^4 + 1, 7*u^6 + 17*u^4 + 7*u^2, 0,
        u^14 + 14*u^12 + 63*u^10 + 100*u^8 + 63*u^6 + 14*u^4 + u^2, 0 ]);
    P2<X,Y,Z> := Ambient(E0);
    B_E_E0 := [
        u*(u^2+1)*(u^4 + 6*u^2 + 1)*(-(3*u^2 + 1)*(X0 - X1) + (u^2 + 3)*u*(X2 - X3)),
        u*(u^2+1)*(u^4 + 6*u^2 + 1)*((u^6 + 2*u^4 + 1)*X0 +
        (-2*u^4 + u^2 - 3)*u^2*X1 +
        -(u^6 + 2*u^2 + 1)*u*X2 + (3*u^4 - u^2 + 2)*u*X3),
        (u^2 + 3)*u*(X0 - X1) - (3*u^2 + 1)*(X2 - X3) ];
    B_E0_E := [ [
        (3*u^8 - 11*u^6 - 6*u^4 - u^2)*X^2 - Y^2
        + (2*u^16 + 8*u^14 - 48*u^12 - 186*u^10 - 188*u^8 - 62*u^6 - 6*u^4)*X*Z
        + (2*u^12 + 12*u^10 + 2*u^8 + 2*u^6 + 12*u^4 + 2*u^2)*Y*Z
        + (-u^22 - 21*u^20 - 168*u^18 - 640*u^16 - 1218*u^14 - 1218*u^12 - 640*u^10 - 168*u^8 - 21*u^6 - u^4)*Z^2,
        (-3*u^8 - 4*u^6 - 6*u^4 - 2*u^2)*X^2 + (3*u^4 - 2*u^2 - 1)*X*Y - Y^2
        + (-9*u^14 - 75*u^12 - 156*u^10 - 156*u^8 - 75*u^6 - 9*u^4)*X*Z
        + (3*u^12 + 21*u^10 + 20*u^8 - 4*u^6 - 7*u^4 - u^2)*Y*Z
        + (-u^22 - 21*u^20 - 168*u^18 - 640*u^16 - 1218*u^14 - 1218*u^12 - 640*u^10 - 168*u^8 - 21*u^6 - u^4)*Z^2,
        (3*u^7 + 2*u^5 + 9*u^3 + u)*X^2 + (-2*u^5 + 2*u)*X*Y + u*Y^2
        + (2*u^15 + 18*u^13 + 58*u^11 + 150*u^9 + 172*u^7 + 72*u^5 + 8*u^3)*X*Z
        + (-4*u^11 - 26*u^9 - 14*u^7 + 10*u^5 + 2*u^3)*Y*Z
        + (u^21 + 21*u^19 + 168*u^17 + 640*u^15 + 1218*u^13 + 1218*u^11 + 640*u^9 + 168*u^7 + 21*u^5 + u^3)*Z^2,
        (-2*u^9 + 10*u^5 + 6*u^3 + u)*X^2 + (-u^5 + 2*u^3 - u)*X*Y + u*Y^2
        + (-4*u^15 - 17*u^13 + 65*u^11 + 192*u^9 + 172*u^7 + 65*u^5 + 7*u^3)*X*Z
        + (-u^11 - 7*u^9 - 8*u^7 - 8*u^5 - 7*u^3 - u)*Y*Z
        + (u^21 + 21*u^19 + 168*u^17 + 640*u^15 + 1218*u^13 + 1218*u^11 + 640*u^9 + 168*u^7 + 21*u^5 + u^3)*Z^2
        ],
        [
        (3*u^6 - 11*u^4 - 6*u^2 - 1)*X*Y + (2*u^2 - 1)*Y^2
        + (-u^18 - u^16 + 49*u^14 + 135*u^12 + 75*u^10 - 20*u^8 - 4*u^6 + 6*u^4 + u^2)*X*Z
        + (-u^14 - 12*u^12 - 54*u^10 - 119*u^8 - 82*u^6 - 5*u^4 + u^2)*Y*Z
        + (2*u^24 + 41*u^22 + 315*u^20 + 1112*u^18 + 1796*u^16 + 1218*u^14 + 62*u^12 - 304*u^10 - 126*u^8 - 19*u^6 - u^4)*Z^2,
        (3*u^10 + 19*u^8 + 6*u^6 - 18*u^4 - 9*u^2 - 1)*X^2 + (-3*u^6 - 4*u^4 - 6*u^2 - 2)*X*Y + (2*u^2 - 1)*Y^2
        + (15*u^16 + 137*u^14 + 319*u^12 + 149*u^10 - 180*u^8 - 164*u^6 - 34*u^4 - 2*u^2)*X*Z
        + (-3*u^14 - 29*u^12 - 81*u^10 - 89*u^8 - 50*u^6 - 18*u^4 - 2*u^2)*Y*Z
        + (2*u^24 + 41*u^22 + 315*u^20 + 1112*u^18 + 1796*u^16 + 1218*u^14 + 62*u^12 - 304*u^10 - 126*u^8 - 19*u^6 - u^4)*Z^2,
        (-3*u^9 - 18*u^7 + 18*u^3 + 3*u)*X^2 + (u^7 + 9*u^5 + 2*u^3 + 3*u)*X*Y + (-2*u^3 + u)*Y^2
        + (-u^17 - 27*u^15 - 173*u^13 - 307*u^11 - 75*u^9 + 192*u^7 + 128*u^5 + 22*u^3 + u)*X*Z
        + (5*u^13 + 38*u^11 + 64*u^9 + 83*u^7 + 66*u^5 + 15*u^3 + u)*Y*Z
        + (-2*u^23 - 41*u^21 - 315*u^19 - 1112*u^17 - 1796*u^15 - 1218*u^13 - 62*u^11 + 304*u^9 + 126*u^7 + 19*u^5 + u^3)*Z^2,
        (u^11 + 6*u^9 - 6*u^5 - u^3)*X^2 + (-u^7 + 6*u^5 + 10*u^3)*X*Y + (-2*u^3 + u)*Y^2
        + (2*u^17 + 13*u^15 - 13*u^13 - 147*u^11 - 149*u^9 + 8*u^7 + 40*u^5 + 6*u^3)*X*Z
        + (-u^13 + 3*u^11 + 71*u^9 + 125*u^7 + 66*u^5 + 8*u^3)*Y*Z
        + (-2*u^23 - 41*u^21 - 315*u^19 - 1112*u^17 - 1796*u^15 - 1218*u^13 - 62*u^11 + 304*u^9 + 126*u^7 + 19*u^5 + u^3)*Z^2
        ]
        ];
    E`WeierstrassMorphism := map< E->E0 | B_E_E0, B_E0_E >;
    /*
    G := GenericPoint(E);
    T := E![u,-1,-1,u]; // Element of order 4
    tau_T := map< E->E | [X3,X0,X1,X2] >;
    tau_T(G) eq G + T;
    S := E![-1,1,u,-u];
    tau_S := map< E->E | [X0,-X1,X2,-X3] >;
    tau_S(G) eq G + S;
    */
    ExE := ProductScheme(E,2);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := Ambient(ExE);
    u0 := 1; u1 := u;
    // 8M for the forms:
    // (A,B,C,D) = ( X0*Y0 + X2*Y2, X0*Y1 + X2*Y3, X1*Y1 + X3*Y3, X1*Y2 + X3*Y0 )
    // 4M + 4m for the products
    // [ u0*A*B + u1*C*D, u0*B*C + u1*A*D, u0*C*D + u1*A*B, u0*A*D + u1*B*C ]
    // The forms are permuted by tau_T^-1 (tau_T x id) and tau_T^-1 (id x tau_T):
    //
    // The transformation from semisplit Z/4Z-normal form is:
    // [   u0*X0 + u1*X2,   u0*X3 + u1*X1,-(u0*X2 + u1*X0), u0*X1 + u1*X3 ]
    // and inverse
    // [ -(u0*X0 + u1*X2), -u0*X3 + u1*X1,  u0*X2 + u1*X0, -u0*X1 + u1*X3 ]
    //
    BB := [
        [
        u0*(X1*Y3 + X3*Y1)*(X1*Y0 + X3*Y2) + u1*(X0*Y2 + X2*Y0)*(X0*Y3 + X2*Y1),
        u0*(X0*Y2 + X2*Y0)*(X1*Y0 + X3*Y2) + u1*(X1*Y3 + X3*Y1)*(X0*Y3 + X2*Y1),
        u0*(X0*Y2 + X2*Y0)*(X0*Y3 + X2*Y1) + u1*(X1*Y3 + X3*Y1)*(X1*Y0 + X3*Y2),
        u0*(X1*Y3 + X3*Y1)*(X0*Y3 + X2*Y1) + u1*(X1*Y0 + X3*Y2)*(X0*Y2 + X2*Y0)
        ],
        [
        u0*(X0*Y0 + X2*Y2)*(X0*Y1 + X2*Y3) + u1*(X1*Y1 + X3*Y3)*(X1*Y2 + X3*Y0),
        u0*(X1*Y1 + X3*Y3)*(X0*Y1 + X2*Y3) + u1*(X0*Y0 + X2*Y2)*(X1*Y2 + X3*Y0),
        u0*(X1*Y1 + X3*Y3)*(X1*Y2 + X3*Y0) + u1*(X0*Y0 + X2*Y2)*(X0*Y1 + X2*Y3),
        u0*(X0*Y0 + X2*Y2)*(X1*Y2 + X3*Y0) + u1*(X1*Y1 + X3*Y3)*(X0*Y1 + X2*Y3)
        ],
        [
        u0*(X0*Y0 + X2*Y2)*(X1*Y0 + X3*Y2) + u1*(X1*Y1 + X3*Y3)*(X0*Y3 + X2*Y1),
        u0*(X1*Y1 + X3*Y3)*(X1*Y0 + X3*Y2) + u1*(X0*Y0 + X2*Y2)*(X0*Y3 + X2*Y1),
        u0*(X1*Y1 + X3*Y3)*(X0*Y3 + X2*Y1) + u1*(X0*Y0 + X2*Y2)*(X1*Y0 + X3*Y2),
        u0*(X0*Y0 + X2*Y2)*(X0*Y3 + X2*Y1) + u1*(X1*Y1 + X3*Y3)*(X1*Y0 + X3*Y2)
        ],
        [
        u0*(X0*Y1 + X2*Y3)*(X1*Y3 + X3*Y1) + u1*(X0*Y2 + X2*Y0)*(X1*Y2 + X3*Y0),
        u0*(X0*Y1 + X2*Y3)*(X0*Y2 + X2*Y0) + u1*(X1*Y3 + X3*Y1)*(X1*Y2 + X3*Y0),
        u0*(X1*Y2 + X3*Y0)*(X0*Y2 + X2*Y0) + u1*(X1*Y3 + X3*Y1)*(X0*Y1 + X2*Y3),
        u0*(X1*Y2 + X3*Y0)*(X1*Y3 + X3*Y1) + u1*(X0*Y2 + X2*Y0)*(X0*Y1 + X2*Y3)
        ]
        ];
    // This gives a 12M + 4m algorithm, and the pair forms a complete system.
    mu_E := map< ExE->E | BB >;
    E`AdditionMorphism := mu_E;
    return E; //T;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Twisted Semisplit Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Semisplit_C4_NormalForm(c::RngElt) -> Crv
    {}
    K := Parent(c);
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    if Characteristic(K) eq 2 then
        return EllipticCurve_Twisted_C4_NormalForm(PP,c,1);
    end if;
    return EllipticCurve_Twisted_Semisplit_C4_NormalForm(PP,c,1);
end intrinsic;

intrinsic EllipticCurve_Twisted_Semisplit_C4_NormalForm(c::RngElt,a::RngElt) -> Crv
    {}
    K := Parent(c);
    bool, a := IsCoercible(K,a);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    if Characteristic(K) eq 2 then
        return EllipticCurve_Twisted_C4_NormalForm(PP,c,a);
    end if;
    return EllipticCurve_Twisted_Semisplit_C4_NormalForm(PP,c,a);
end intrinsic;

intrinsic EllipticCurve_Twisted_Semisplit_C4_NormalForm(PP::Prj,c::RngElt) -> Crv
    {}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    if Characteristic(K) eq 2 then
        return EllipticCurve_Twisted_C4_NormalForm(PP,c,1);
    end if;
    return EllipticCurve_Twisted_Semisplit_C4_NormalForm(PP,c,1);
end intrinsic;

intrinsic EllipticCurve_Twisted_Semisplit_C4_NormalForm(PP::Prj,c::RngElt,a::RngElt) -> Crv
    {The twist (by x^2 + x + a = 0 [default a = 1]) of the  the elliptic curve
    in semisplit Z/4Z-normal form: X0^2 - X1^2 + X2^2 - X3^2 = c X0 X2 = c X1 X3, given
    by (X0,X1,X2,X3) -> (w1 X0 + w1 X3, w1 X1 + w2 X2, w2 X1 + w1 X2, w2 X0 + w1 X3),
    where \{w1,w2\} are the roots of x^2 + x + a = 0.}

    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    require Characteristic(K) eq 2: "Not implemented: Base ring of argument 1 must be of characteristic 2.";
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    bool, a := IsCoercible(K,a);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    if a eq 0 then
        return EllipticCurve_Semisplit_C4_NormalForm(PP,c);
    end if;
    if Characteristic(K) eq 2 then
        return EllipticCurve_Twisted_C4_NormalForm(PP,c,a);
    end if;
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    require Characteristic(K) eq 2: "Not implemented : Base ring of argument 1 must be of characteristic 2.";
    /*
    ET := Curve(PP,[ (X0 + X1 + X2 + X3)^2 + c*(X0*X2 + a*(X0*X1 + X2*X3)), X0*X2 + X1*X3 ]);
    ET`EllipticModelType := "Twisted semisplit Z/4Z-normal form";
    ET`EllipticModelInvariants := [c,a];
    ET`IdentityElement := [1,0,0,1];
    ET`EmbeddingClass := [0,1,1,0];
    P1 := Curve(ProjectiveSpace(K,1));
    ET`KummerMorphism := map< ET->P1 | [[X0,X1],[X3,X2]] >;
    E0 := EllipticCurve([1,a,0,0,1/c^4]);
    P2<X,Y,Z> := AmbientSpace(E0);
    iso_ET_E0 := map< ET->E0 |
        [
        [ c*(X0 + X3), c*X0 + X1 + X2, c^2*(X1 + X2) ],
        [ c*X0*X1, X0^2 + X0*X3 + X1*X2 + c*(a + 1)*X0*X1 + a*c*X0*X2, c^2*X1^2 ],
        [ c*(X1 + X2)^2, X0*X1 + X2*X3 + c*(a + 1)*X1^2 + a*c*X2^2, c^2*(X0*X1 + a*c*X1^2 + c*X1*X2 + a*c*X2^2 + X2*X3) ],
        [ c*X1*X3, X2^2 + X0*X3 + X3^2 + c*(a + 1)*X1*X3 + a*c*X2*X3, c^2*X1*X2 ],
        [ c*X2*X3, X0*X3 + X1*X2 + X3^2 + a*c*(X1 + X2)*X3, c^2*X2^2 ]
        ],
        [
        [ c*X*(c^2*Y + Z), Z*(c^2*Y + Z), Z*(c^2*(X + Y) + Z), c*X*(c^2*(X + Y) + Z) ],
        [ (c^2*Y + Z)^2, c^3*(X^2 + a*X*Z + Y*Z), c*(c^2*X^2 + a*c^2*X*Z + Z^2), c^4*(X + Y)*Y + (c^2*X + Z)*Z ]
        ] >;
    ET`WeierstrassMorphism := iso_ET_E0;
    ETxET := ProductScheme(ET,ET);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(ETxET);
    BB_pi1 := [
        [
        X0*Y3 + X1*Y2 + X2*Y1 + X3*Y0,
        X0*Y1 + X1*Y0 + X2*Y3 + X3*Y2
        ],
        [
        X1*Y2 + X3*Y0 + a*(X0*Y0 + X1*Y1 + X2*Y2 + X3*Y3),
        X0*Y1 + X2*Y3 + a*(X0*Y2 + X1*Y3 + X2*Y0 + X3*Y1)
        ]
        ];
    BB_pi2 := [
        [
        X0*Y0 + X2*Y2 + a*((X0 + X3)*(Y0 + Y3) + (X1 + X2)*(Y1 + Y2)),
        X1*Y1 + X3*Y3 + a*((X0 + X3)*(Y0 + Y3) + (X1 + X2)*(Y1 + Y2))
        ],
        [
        X1*Y3 + X3*Y1 + a*((X0 + X3)*(Y1 + Y2) + (X1 + X2)*(Y0 + Y3)),
        X0*Y2 + X2*Y0 + a*((X0 + X3)*(Y1 + Y2) + (X1 + X2)*(Y0 + Y3))
        ]
        ];
    P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
    E1 := Curve(P1xP1,((U0 + U1)*(V0 + V1))^2 + c*U0*U1*(V0*V1 + a*(V0 + V1)^2));
    mu_pixpi := map< ETxET->E1 | [ S1 cat S2 : S1 in BB_pi1, S2 in BB_pi2 ] >;
    SkewSegre := map< E1->ET | [ U0*V0, U1*V0, U1*V1, U0*V1 ] >;
    ET`AdditionMorphism := mu_pixpi * SkewSegre;
    return ET;
    */
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Twisted Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_C4_NormalForm(c::RngElt) -> Crv
    {}
    K := Parent(c);
    require Characteristic(K) eq 2: "Base ring of argument 1 must be of characteristic 2.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Twisted_C4_NormalForm(PP,c,1);
end intrinsic;

intrinsic EllipticCurve_Twisted_C4_NormalForm(c::RngElt,a::RngElt) -> Crv
    {}
    K := Parent(c);
    bool, a := IsCoercible(K,a);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    require Characteristic(K) eq 2: "Base ring of argument 1 must be of characteristic 2.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Twisted_C4_NormalForm(PP,c,a);
end intrinsic;

intrinsic EllipticCurve_Twisted_C4_NormalForm(PP::Prj,c::RngElt) -> Crv
    {}
    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require Characteristic(K) eq 2: "Base ring of argument 1 must be of characteristic 2.";
    return EllipticCurve_Twisted_C4_NormalForm(PP,c,1);
end intrinsic;

intrinsic EllipticCurve_Twisted_C4_NormalForm(PP::Prj,c::RngElt,a::RngElt) -> Crv
    {The twist (by x^2 + x + a = 0 [default a = 1]) of the  the elliptic curve
    in Z/4Z-normal form: (X0 + X1 + X2 + X3)^2 = c X0 X2 = c X1 X3, given
    by (X0,X1,X2,X3) -> (w1 X0 + w1 X3, w1 X1 + w2 X2, w2 X1 + w1 X2, w2 X0 + w1 X3),
    where \{w1,w2\} are the roots of x^2 + x + a = 0.}

    require Dimension(PP) eq 3: "Argument 1 must be a projective space of dimension 3.";
    K := BaseRing(PP);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    bool, a := IsCoercible(K,a);
    require bool: "Argument 3 must be coercible into the base ring of argument 1.";
    if a eq 0 then
        return EllipticCurve_C4_NormalForm(PP,c);
    end if;
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    require Characteristic(K) eq 2: "Not implemented : Base ring of argument 1 must be of characteristic 2.";
    ET := Curve(PP,[ (X0 + X1 + X2 + X3)^2 + c*(X0*X2 + a*(X0*X1 + X2*X3)), X0*X2 + X1*X3 ]);
    ET`EllipticModelType := "Twisted Z/4Z-normal form";
    ET`EllipticModelInvariants := [c,a];
    ET`IdentityElement := [1,0,0,1];
    ET`EmbeddingClass := [0,1,1,0];
    ET`InverseMorphism := map< ET->ET | [X3,X2,X1,X0], [X3,X2,X1,X0] >;
    ET`KummerMorphism := map< ET->Curve(ProjectiveSpace(K,1)) | [[X0,X1],[X3,X2]] >;
    E0 := EllipticCurve([1,a,0,0,1/c^4]);
    P2<X,Y,Z> := AmbientSpace(E0);
    iso_ET_E0 := map< ET->E0 |
        [
        [ c*(X0 + X3), c*X0 + X1 + X2, c^2*(X1 + X2) ],
        [ c*X0*X1, X0^2 + X0*X3 + X1*X2 + c*(a + 1)*X0*X1 + a*c*X0*X2, c^2*X1^2 ],
        [ c*(X1 + X2)^2, X0*X1 + X2*X3 + c*(a + 1)*X1^2 + a*c*X2^2, c^2*(X0*X1 + a*c*X1^2 + c*X1*X2 + a*c*X2^2 + X2*X3) ],
        [ c*X1*X3, X2^2 + X0*X3 + X3^2 + c*(a + 1)*X1*X3 + a*c*X2*X3, c^2*X1*X2 ],
        [ c*X2*X3, X0*X3 + X1*X2 + X3^2 + a*c*(X1 + X2)*X3, c^2*X2^2 ]
        ],
        [
        [ c*X*(c^2*Y + Z), Z*(c^2*Y + Z), Z*(c^2*(X + Y) + Z), c*X*(c^2*(X + Y) + Z) ],
        [ (c^2*Y + Z)^2, c^3*(X^2 + a*X*Z + Y*Z), c*(c^2*X^2 + a*c^2*X*Z + Z^2), c^4*(X + Y)*Y + (c^2*X + Z)*Z ]
        ] >;
    ET`WeierstrassMorphism := iso_ET_E0;
    ETxET := ProductScheme(ET,ET);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(ETxET);
    BB_pi1 := [
        [
        X0*Y3 + X1*Y2 + X2*Y1 + X3*Y0,
        X0*Y1 + X1*Y0 + X2*Y3 + X3*Y2
        ],
        [
        X1*Y2 + X3*Y0 + a*(X0*Y0 + X1*Y1 + X2*Y2 + X3*Y3),
        X0*Y1 + X2*Y3 + a*(X0*Y2 + X1*Y3 + X2*Y0 + X3*Y1)
        ]
        ];
    BB_pi2 := [
        [
        X0*Y0 + X2*Y2 + a*((X0 + X3)*(Y0 + Y3) + (X1 + X2)*(Y1 + Y2)),
        X1*Y1 + X3*Y3 + a*((X0 + X3)*(Y0 + Y3) + (X1 + X2)*(Y1 + Y2))
        ],
        [
        X1*Y3 + X3*Y1 + a*((X0 + X3)*(Y1 + Y2) + (X1 + X2)*(Y0 + Y3)),
        X0*Y2 + X2*Y0 + a*((X0 + X3)*(Y1 + Y2) + (X1 + X2)*(Y0 + Y3))
        ]
        ];
    P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
    E1 := Curve(P1xP1,((U0 + U1)*(V0 + V1))^2 + c*U0*U1*(V0*V1 + a*(V0 + V1)^2));
    mu_pixpi := map< ETxET->E1 | [ S1 cat S2 : S1 in BB_pi1, S2 in BB_pi2 ] >;
    SkewSegre := map< E1->ET | [ U0*V0, U1*V0, U1*V1, U0*V1 ] >;
    ET`AdditionMorphism := mu_pixpi * SkewSegre;
    return ET;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// (Mu_2 x ZZ/2ZZ)-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Mu2xC2_NormalForm(r::RngElt) -> Crv
    {}
    K := Parent(r);
    if Type(K) eq RngInt then K := RationalField(); r := K!r; end if;
    require IsUnit(r) and r ne 16: "Argument 2 must be a unit different from 16.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Mu2xC2_NormalForm(PP,r);
end intrinsic;

intrinsic EllipticCurve_Mu2xC2_NormalForm(PP::Prj,r::RngElt) -> Crv
    {An elliptic curve in (mu_2 x Z/2Z)-normal form, given
    by (X0 - X2)^2 = X1*X3, (X1 - X3)^2 = r*X0*X2, with
    identity (1:1:0:1).}
    K := BaseRing(PP);
    bool, r := IsCoercible(K,r);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(r) and r ne 16: "Argument 2 must be a unit different from 16.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    EE := Curve(PP,[ (X0 - X2)^2 - X1*X3, (X1 - X3)^2 - r*X0*X2 ]);
    EE`EllipticModelType := "(Mu_2 x Z/2Z)-normal form";
    EE`EllipticModelInvariants := [r];
    EE`IdentityElement := [1,1,0,1];
    EE`EmbeddingClass := [1,1,0,1];
    EE`InverseMorphism := map< EE->EE | [ X0, X3, X2, X1 ] >;
    E0 := EllipticCurve([1,4/r,0,1/r,0]);
    P2<X,Y,Z> := AmbientSpace(E0);
    // This system has a base point at O:
    if Characteristic(K) eq 2 then
        BB_EE_E0 := [X1+X3, X0+X2+X3, r*X2];
        BB_E0_EE := [
            [r*X^2,r*(X^2+X*Z+Y*Z)+Z^2, Z^2, r*(X^2+Y*Z)+Z^2],
            [r*(X*Y+Y^2)+X*Z,r*(X^2+Y^2),X*Z,r*Y^2]];
    else
        BB_EE_E0 := [
            r*(X1 + X3 - 2*(X0 + X2)),
            r*(X0 + X2 - X3) - 8*(X1 - X3),
            r^2*X2 - 4*r*(X1 + X3 - 2*(X0 - X2)) ];
        BB_E0_EE := [
            [X*(r*X + 4*Z),r*(X*(X + Z) + Y*Z) + Z^2,(4*X + Z)*Z,r*(X^2-Y*Z) + Z^2],
            [r*(X + Y)*Y - X*Z,(r-4)*X^2 + r*(2*X + Y)*Y,(4*X + Z)*X,-4*X^2 + r*Y^2]];
    end if;
    EE`WeierstrassMorphism := map< EE->E0 | BB_EE_E0, BB_E0_EE >;
    P1<U,V> := Curve(ProjectiveSpace(K,1));
    if Characteristic(K) eq 2 then
        EE`KummerMorphism := map< EE->P1 | [[X0,X1+X3],[X1+X3,r*X2]] >;
    else
        EE`KummerMorphism := map< EE->P1 | [X0,X1+X3] >;
    end if;
    EExEE := ProductScheme(EE,2);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(EExEE);
    F := (X0^2+X2^2)*Y1*Y3 - X1*X3*(Y0^2+Y2^2)
        - (X0^2*Y3^2 - X3^2*Y0^2) + (X1^2*Y2^2 - X2^2*Y1^2);
    G := (X1^2+X3^2)*Y1*Y3 - X1*X3*(Y1^2+Y3^2);
    // This is just one addition law -- construct a complete set with automorphisms?
    BB := [
        [(X0*Y0 - X2*Y2)*(X3*Y1 - X1*Y3), F-G, (X1*Y1 - X3*Y3)*(X0*Y2 - X2*Y0), F]
        ];
    EE`AdditionMorphism := map< EExEE->EE | BB >;
    return EE;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Split (Mu_2 x ZZ/2ZZ)-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Split_Mu2xC2_NormalForm(c::RngElt) -> Crv
    {}
    K := Parent(c);
    if Type(K) eq RngInt then K := RationalField(); c := K!c; end if;
    require IsUnit(c) and c ne 2 and c ne -2 and c^2+4 ne 0 :
        "Argument must be a unit different from 2, -2 and the roots of x^2+4.";
    PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    return EllipticCurve_Split_Mu2xC2_NormalForm(PP,c);
end intrinsic;

intrinsic EllipticCurve_Split_Mu2xC2_NormalForm(PP::Prj,c::RngElt) -> Crv
    {An elliptic curve in split (mu_2 x Z/2Z)-normal form, given
    by (X0 - X2)^2 = c^2*X1*X3, (X1 - X3)^2 = c^2*X0*X2, with
    identity (c:1:0:1).}
    K := BaseRing(PP);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible into the base ring of argument 1.";
    require IsUnit(c) and c ne 2 and c ne -2 and c^2+4 ne 0 :
        "Argument must be a unit different from 2, -2 and the roots of x^2+4.";
    X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    EE := Curve(PP,[ (X0 - X2)^2 - c^2*X1*X3, (X1 - X3)^2 - c^2*X0*X2 ]);
    EE`EllipticModelType := "Split (mu_2 x Z/2Z)-normal form";
    EE`EllipticModelInvariants := [c];
    EE`IdentityElement := [c,1,0,1];
    EE`EmbeddingClass := [c,1,0,1];
    EE`InverseMorphism := map< EE->EE | [ X0, X3, X2, X1 ] >;
    E0 := EllipticCurve([1,4/c^4,0,1/c^4,0]);
    P2<X,Y,Z> := AmbientSpace(E0);
    BB_EE_E0 := [
        2*(X0 + X2) - c*(X1 + X3),
        -(X0 + X2) + ((c^4 - 8)*X1 + 8*X3)/c^3,
        -8*X0 - (c^4 - 8)*X2 + 4*c*(X1 + X3)
        ];
    BB_E0_EE := [
        [
        c*X*(c^4*X + 4*Z),
        c^4*(X^2 - Y*Z) + Z^2,
        c*(4*X + Z)*Z,
        c^4*(X^2 + X*Z + Y*Z) + Z^2
        ],
        [
        c*(c^4*(X + Y)*Y - X*Z),
        -4*X^2 + c^4*Y^2,
        c*X*(4*X + Z),
        -4*X^2 + c^4*(X + Y)^2
        ]
        ];
    EE`WeierstrassMorphism := map< EE->E0 | BB_EE_E0, BB_E0_EE >;
    EExEE := ProductScheme(EE,2);
    PPxPP<X0,X1,X2,X3,Y0,Y1,Y2,Y3> := AmbientSpace(EExEE);
    // 8M to compute these eight forms (char not 2):
    /*
    LL :=  [
        X0*Y0 - X2*Y2, X0*Y2 - X2*Y0,
        X0*Y1 - X2*Y3, X0*Y3 - X2*Y1,
        X1*Y0 - X3*Y2, X1*Y2 - X3*Y0,
        X1*Y1 - X3*Y3, X1*Y3 - X3*Y1
        ];
    */
    // 4M for the rest (or 2M + 4S in char 2):
    BB := [
        [
        c*(X0*Y0 - X2*Y2)*(X1*Y3 - X3*Y1),
        (X1*Y0 - X3*Y2)^2 - (X0*Y1 - X2*Y3)^2,
        -c*(X1*Y1 - X3*Y3)*(X0*Y2 - X2*Y0),
        (X0*Y3 - X2*Y1)^2 - (X1*Y2 - X3*Y0)^2
        ],
        [
        (X0*Y0 - X2*Y2)^2 - (X1*Y3 - X3*Y1)^2,
        c*(X0*Y1 - X2*Y3)*(X1*Y0 - X3*Y2),
        (X1*Y1 - X3*Y3)^2 - (X0*Y2 - X2*Y0)^2,
        -c*(X0*Y3 - X2*Y1)*(X1*Y2 - X3*Y0)
        ]
        ];
    EE`AdditionMorphism := map< EExEE->EE | BB >;
    return EE;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Kummer-oriented product elliptic curves
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_MontgomeryOriented_C4_KummerProduct(e::RngElt,tt::[RngElt]) -> Crv
    {A Kummer-oriented product elliptic curve in P1xP1, suitable for Montgomery morphism.}
    K := Universe(tt);
    bool, e := IsCoercible(K,e);
    require bool: "Argument 1 must be coercible with universe of argument 2.";
    require #tt eq 2: "Argument 2 must be a sequence of length 2.";
    P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
    return EllipticCurve_MontgomeryOriented_C4_KummerProduct(P1xP1,e,tt);
end intrinsic;

intrinsic EllipticCurve_MontgomeryOriented_C4_KummerProduct(P1xP1,e::RngElt,tt::[RngElt]) -> Crv
    {A Kummer-oriented product elliptic curve in P1xP1, suitable for Montgomery morphism.}
    K := BaseRing(P1xP1);
    bool, e := IsCoercible(K,e);
    require bool: "Argument 2 must be coercible to the base ring of argument 1.";
    bool, tt := CanChangeUniverse(tt,K);
    require bool: "Argument 3 must be compatible with the base ring of argument 1.";
    require Type(P1xP1) eq PrjProd and Gradings(P1xP1) eq [[1,1,0,0],[0,0,1,1]]: "Argument 3 must be a product of projective lines.";
    U0,U1,V0,V1 := Explode([ P1xP1.i : i in [1..4] ]);
    t0, t1 := Explode(tt);
    K2 := Curve(P1xP1,t1^2*(U0*V0-U1*V1)^2 + t0^2*(U0*V1-U1*V0)^2 - t0*t1*(e*U0*U1*V0*V1 + 2*(U0*V0+U1*V1)*(U0*V1+U1*V0)));
    K2`EllipticModelType := "Kummer-oriented product";
    K2`EllipticModelType := "Montgomery-oriented Z/4Z Kummer product";
    K2`EllipticModelInvariants := [e,t0,t1];
    K2`IdentityElement := [1,0,t0,t1];
    K2`MontgomeryBasePoint := [t0,t1,1,0];
    B1 := [(U0^2 - U1^2)^2, e*U0^2*U1^2 + 4*U0*U1*(U0^2 + U1^2)];
    B2 := [t1*(U0*V0-U1*V1)^2,t0*(U0*V1-U1*V0)^2];
    K2`MontgomeryMorphism := map< K2->K2 | B1 cat B2 >;
    K2`MontgomeryInversion := map< K2->K2 | [V0,V1,U0,U1] >;
    return K2;
end intrinsic;

intrinsic EllipticCurve_MontgomeryOriented_Mu4_KummerProduct(c::RngElt,tt::[RngElt]) -> Crv
    {A Kummer-oriented product elliptic curve in P1xP1, suitable for Montgomery morphism.}
    K := Universe(tt);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 1 must be coercible with universe of argument 2.";
    require #tt eq 2: "Argument 2 must be a sequence of length 2.";
    P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
    return EllipticCurve_MontgomeryOriented_Mu4_KummerProduct(P1xP1,c,tt);
end intrinsic;

intrinsic EllipticCurve_MontgomeryOriented_Mu4_KummerProduct(P1xP1,c::RngElt,tt::[RngElt]) -> Crv
    {A Kummer-oriented product elliptic curve in P1xP1, suitable for Montgomery morphism.}
    K := BaseRing(P1xP1);
    bool, c := IsCoercible(K,c);
    require bool: "Argument 2 must be coercible to the base ring of argument 1.";
    bool, tt := CanChangeUniverse(tt,K);
    require bool: "Argument 3 must be compatible with the base ring of argument 1.";
    require Type(P1xP1) eq PrjProd and Gradings(P1xP1) eq [[1,1,0,0],[0,0,1,1]]: "Argument 3 must be a product of projective lines.";
    U0,U1,V0,V1 := Explode([ P1xP1.i : i in [1..4] ]);
    t0, t1 := Explode(tt); u := 4/c^4;
    h1 := U0^2*V1^2 + U1^2*V0^2 - u*(U0^2*V0^2 + U1^2*V1^2);
    h0 := U0^2*V0^2 + U1^2*V1^2 - u*(U0^2*V1^2 + U1^2*V0^2);
    hh := t0^2*h1 + t1^2*h0 - c^2*(1-u^2)*t0*t1*U0*U1*V0*V1;
    K2 := Curve(P1xP1,hh);
    K2`EllipticModelType := "Montgomery-oriented mu_4 Kummer product";
    K2`EllipticModelInvariants := [c,t0,t1];
    K2`IdentityElement := [1,0,t0,t1];
    K2`MontgomeryBasePoint := [t0,t1,1,0];
    if Characteristic(K) eq 2 then
        B1 := [ U0^4 + U1^4, c^2*U0^2*U1^2 ];
    else
        B1 := [ U0^4 + U1^4 - 8/c^4*U0^2*U1^2, c^2*U0^2*U1^2 - (2/c^2)*(U0^4 + U1^4) ];
    end if;
    // [ X3*Y1 + X1*Y3, X2*Y0 + X0*Y2 ]

    B2 := [t1*(U0*V0-U1*V1)^2,t0*(U0*V1-U1*V0)^2];
    /*
    (U0,U1) = [[c*X0,X1+X3],[X1-X3,c*X2]];
    (V0,V1) = [[X0*Y0+X2*Y2,X1*Y1+X3*Y3],[X3*Y1-X1*Y3,X0*Y2-X2*Y0]];
    [ [ X1*Y3 - X3*Y1, X2*Y0 - X0*Y2 ], [ X0*Y0 + D*X2*Y2, X1*Y1 + X3*Y3 + 2*a*(X1 - X3)*(Y1 - Y3) ] ]
    */
    K2`MontgomeryMorphism := map< K2->K2 | B1 cat B2 >;
    K2`MontgomeryInversion := map< K2->K2 | [V0,V1,U0,U1] >;
    return K2;
end intrinsic;

