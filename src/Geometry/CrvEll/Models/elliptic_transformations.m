//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2015 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Simplified imput for scaling transformation of Weierstrass models
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic Transformation(E::CrvEll,a::RngElt) -> CrvEll, MapIsoSch
    {The transformation of E given by (x,y) -> (a^2x,a^3y),
    returning the isomorphic elliptic curve and isomorphism.}
    return Transformation(E,[0,0,0,a]);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Edwards normal form constructors
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function EllipticCurve_Edwards_NormalForm_Constructor(C,oo,pp,qq,rr)
    // Given places (identity) oo, (2-torsion) pp, and (4-torsion) qq and rr,
    // construct the Edwards model
    //
    //    X0^2 + d*X3^2 = aX1^2 + X2^2
    //    X0*X3 = X1*X2,
    //
    // with embedding :
    //                      X_0 X_1 X_2 X_3
    // oo := Place(O) : O = ( 0 : 1 : 0 : 1 )
    // pp := Place(P) : P = ( 0 :-1 : 0 : 1 ) = 2Q
    // qq := Place(Q) : Q = ( 1 : 0 : 0 : 1 )
    // rr := Place(R) : R = (-1 : 0 : 0 : 1 ) = -Q
    K := BaseRing(C);
    V1, m1 := RiemannRochSpace(2*qq-oo-pp); assert Dimension(V1) eq 1;
    u := m1(V1.1); // = x/(x-1)
    u *:= 1/(2*Evaluate(u,rr));
    x := u/(u-1);
    V2, m2 := RiemannRochSpace(2*(oo-pp));  assert Dimension(V2) eq 1;
    v := m2(V2.1); // = (1 + y)/(1 - y)
    v *:= 1/Evaluate(v,qq); //
    y := (v - 1)/(1 + v);
    z := x*y;
    d := 2*Evaluate((y-1)/x^2,oo) + 1;
    E := EllipticCurve_Twisted_Edwards_NormalForm(d,1);
    m := map< C->E | [1,x,y,z] >;
    return E, m;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in Edwards normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Edwards_NormalForm(C::Crv,O::Pt,T::Pt) -> Crv, MapSch
    {Given a genus 1 curve C with base point O and 4-torsion point T,
    returns the Edwards model in PP^3: X0^2 + d*X3^2 = aX1^2 + X2^2, X0*X3 = X1*X2,
    with identity (1:0:1:0) together with the isomorphism from C taking O to
    the identity and T to the 4-torsion point (1:0:0:1).}
    K := BaseField(C);
    require IsUnit(K!2) : "Argument 1 must have base ring in which 2 is a unit.";
    require Scheme(O) eq C : "Argument 2 must be a point on argument 1.";
    require Scheme(T) eq C : "Argument 3 must be a point on argument 1.";
    require O in C(K) : "Argument 2 must be a rational point of argument 1.";
    require T in C(K) : "Argument 3 must be a rational point of argument 1.";
    //
    oo := Place(O);
    qq := Place(T);
    //
    V4T, m4T := RiemannRochSpace(4*oo-4*qq);
    require Dimension(V4T) eq 1 :
        "Argument 3 must be a 4-torsion point (with respect to argument 2 as base point).";
    x4T := m4T(V4T.1); // div(x4T) = 4(T) - 4(O)
    //
    VOS, mOS := RiemannRochSpace(2*qq-oo); assert Dimension(VOS) eq 1;
    xOS := mOS(VOS.1);  // div(xOS) = (O) + (S) - 2(T)
    x2S := xOS^2 * x4T; // div(x2S) = 2(S) - 2(O)
    pp := Zeros(x2S)[1];
    //
    VTR, mTR := RiemannRochSpace(2*oo-qq); assert Dimension(VTR) eq 1;
    xTR := mTR(VTR.1);  // div(xTR) = (T) + (R) - 2(O)
    x4R := xTR^4 / x4T; // div(x4R) =
    rr := Zeros(x4R)[1];
    return EllipticCurve_Edwards_NormalForm_Constructor(C,oo,pp,qq,rr);
end intrinsic;

intrinsic EllipticCurve_Edwards_NormalForm(E::CrvEll,T::PtEll) -> Crv, MapSch
    {}
    require Scheme(T) eq E : "Argument 2 must be a point on argument 1.";
    require T in E(BaseField(E)) : "Argument 2 must be a rational point of argument 1.";
    O := E!0; S := 2*T; U := -T;
    require S ne O and 2*S eq O : "Argument 2 must be a point of order 4.";
    oo := Place(O);  ss := Place(S); tt := Place(T); uu := Place(U);
    return EllipticCurve_Edwards_NormalForm_Constructor(E,oo,ss,tt,uu);
end intrinsic;

intrinsic EllipticCurve_Edwards_NormalForm(C::Crv,T::Pt) -> Crv, MapSch
    {Given an elliptic curve C and 4-torsion point T, returns the
    twisted Edwards normal form E in PP^3: X0^2 + d*X3^2 = aX1^2 + X2^2, X0*X3 = X1*X2,
    with identity (1:0:1:0) together with the isomorphism from C to E
    taking T to the 4-torsion point (1:0:0:1).}

    require Scheme(T) eq C : "Argument 2 must be a point on argument 1.";
    require T in C(BaseField(C)) : "Argument 2 must be a rational point of argument 1.";
    require IsEllipticCurve(C): "Argument 1 must be an elliptic curve model.";
    O := Identity(C);
    if assigned C`EllipticModelType then
        PP := AmbientSpace(C);
        if Dimension(PP) eq 2 then
            X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
        elif Dimension(PP) eq 3 then
            X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
        end if;
        case C`EllipticModelType:
        when "Huff normal form":
            E, iso_C_E := EllipticCurve_Edwards_NormalForm(C);
            if T eq E![1,1,1] then
                return E, iso_C_E;
            elif T eq E![-1,1,1] then
                return E, InverseMorphism(C) * iso_C_E;
            end if;
        when "Z/4Z-normal form":
            E, iso_C_E := EllipticCurve_Edwards_NormalForm(C);
            if T eq E![1,1,0,0] then
                return E, iso_C_E;
            elif T eq E![0,0,-1,1] then
                return E, InverseMorphism(C) * iso_C_E;
            end if;
        when "Semisplit Z/4Z-normal form":
            E, iso_C_E := EllipticCurve_Edwards_NormalForm(C);
            if T eq E![1,1,0,0] then
                return E, iso_C_E;
            elif T eq E![0,0,-1,1] then
                return E, InverseMorphism(C) * iso_C_E;
            end if;
        when "Split Z/4Z-normal form":
            E, iso_C_E := EllipticCurve_Edwards_NormalForm(C);
            u := Explode(E`EllipticModelInvariants);
            if T eq E![1,-u,-u,1] then
                return E, iso_C_E;
            elif T eq E![u,-1,-1,u] then
                return E, InverseMorphism(C) * iso_C_E;
            end if;
        end case;
    end if;
    S := 2*T; U := -T;
    require S ne O and 2*S eq O : "Argument 2 must be a point of order 4.";
    oo := Place(O);  ss := Place(S); tt := Place(T); uu := Place(U);
    return EllipticCurve_Edwards_NormalForm_Constructor(E,oo,ss,tt,uu);
end intrinsic;

intrinsic EllipticCurve_Edwards_NormalForm(C::Crv) -> Crv, MapSch
    {Given an elliptic curve C in some normal form with 4-level structure,
    returns the twisted Edwards normal form E in PP^3: X0^2 + d*X3^2 =
    a X1^2 + X2^2, X0*X3 = X1*X2, with identity (1:0:1:0) together
    with the isomorphism from C to E. In the case of mu_4 normal forms,
    the returned curve is the -1-twisted Edwards norm form (a = -1).}

    require IsEllipticCurve(C): "Argument 1 must be an elliptic curve model.";
    require assigned C`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    require Characteristic(BaseField(C)) ne 2:
        "Argument 1 must be an elliptic curve over a field of characteristic different from 2.";
    O := Identity(C);
    PP := AmbientSpace(C);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case C`EllipticModelType:
    when "Huff normal form":
        a, b := Explode(C`EllipticModelInvariants);
        c := (a-b)/(a+b);
        E := EllipticCurve_Edwards_NormalForm(c^2);
        B1 := [
            [ X0^2 + X1*X2, X0*(X1 + X2), X0^2 - X1*X2, (a + b)/(a - b)*X0*(-X1 + X2) ],
            [
            (a - b)^2*X0*(X1 + X2),
            -(a - b)*(X1 + X2)*(b*X1 - a*X2),
            (a + b)*(a - b)*X0*(X2 - X1),
            (a + b)*(X1 - X2)*(b*X1 - a*X2)
            ]
            ];
        PP<X0,X1,X2,X3> := AmbientSpace(E);
        B2 := [ X0 + X2, X1 - c*X3, X1 + c*X3 ];
        return E, map< C->E | B1, B2 >;
    when "Z/4Z-normal form":
        u := Explode(C`EllipticModelInvariants);
        E := EllipticCurve_Edwards_NormalForm(PP,(u-8)/(u+8));
        B := [ X0 + X1 + X2 + X3, X0 + X1 - X2 - X3, X0 - X1 - X2 + X3, X0 - X1 + X2 - X3 ];
        return E, map< C->E | B, B >;
    when "Semisplit Z/4Z-normal form":
        D, iso_C_D := EllipticCurve_C4_NormalForm(C);
        E, iso_D_E := EllipticCurve_Edwards_NormalForm(D);
        return E, iso_C_D * iso_D_E;
    when "Split Z/4Z-normal form":
        u := Explode(C`EllipticModelInvariants); c := (u+1)/(u-1);
        E := EllipticCurve_Edwards_NormalForm(PP,c^8);
        B1 := [ X0+X1+X2+X3, -1/c*(X0-X1-X2+X3), -1/c*(X0+X1-X2-X3), 1/c^4*(X0-X1+X2-X3) ];
        B2 := [ X0-c*X1-c*X2+c^4*X3, X0+c*X1-c*X2-c^4*X3, X0+c*X1+c*X2+c^4*X3, X0-c*X1+c*X2-c^4*X3 ];
        return E, map< C->E | B1, B2 >;
    when "Mu_4 normal form":
        r := Explode(C`EllipticModelInvariants);
        E := EllipticCurve_Twisted_Edwards_NormalForm(PP,-16*r,-1);
        B1 := [ 4*X0, 2*(X1-X3), 2*(X1+X3), X2 ];
        B2 := [ X0, X1+X2, 4*X3, -X1+X2 ];
        return E, map< C->E | B1, B2 >;
    when "Semisplit mu_4 normal form":
        s := Explode(C`EllipticModelInvariants);
        E := EllipticCurve_Twisted_Edwards_NormalForm(PP,-16/s^2,-1);
        // HERE!!!
        B1 := [ 4*X0, 2*(X1-X3), 2*(X1+X3), X2 ];
        B2 := [ X0, X1+X2, 4*X3, -X1+X2 ];
        return E, map< C->E | B1, B2 >;
    when "Split mu_4 normal form":
        c := Explode(C`EllipticModelInvariants);
        E := EllipticCurve_Twisted_Edwards_NormalForm(PP,-16/c^8,-1);
        // HERE!!!
        B1 := [ 4*X0, 2*(X1-X3), 2*(X1+X3), X2 ];
        B2 := [ X0, X1+X2, 4*X3, -X1+X2 ];
        return E, map< C->E | B1, B2 >;
    when "Twisted mu_4 normal form":
        b, a := Explode(C`EllipticModelInvariants); D := 4*a + 1;
        E := EllipticCurve_Twisted_Edwards_NormalForm(PP,-16*D*b,-D);
        B1 := [ 4*X0, 2*(X1-X3), 2*(X1+X3), X2 ];
        B2 := [ X0, X1+X2, 4*X3, -X1+X2 ];
        return E, map< C->E | B1, B2 >;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Jacobi normal form constructors
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function EllipticCurve_Jacobi_NormalForm_Constructor(C,oo,pp,qq,rr)
    /*
    Given places (identity) oo, (2-torsion) pp, qq and rr, construct the
    Jacobi model:

        aX0^2 + X1^2 = X2^2,
        bX0^2 + X2^2 = X3^2,
        cX0^2 + X3^2 = X1^2,

    with embedding :
                              X_0 X_1 X_2 X_3
        oo := Place(O) : O = ( 0 : 1 : 1 : 1 )
        pp := Place(P) : P = ( 0 :-1 : 1 : 1 )
        qq := Place(Q) : Q = ( 0 : 1 :-1 : 1 )
        rr := Place(R) : R = ( 0 : 1 : 1 :-1 )

    Need to define functions x_i = X_i/X_0, of degree 4, but first set

        u_1 = (X_1 - X_2)/X_0,
        u_2 = (X_2 - X_3)/X_0,
        u_3 = (X_3 - X_1)/X_0 = -(u1 + u2),

    determined by

        div(u_1) = oo + rr - pp - qq,
        div(u_2) = oo + pp - qq - rr,
        div(u_3) = oo + qq - pp - rr,

    such that (u_i/u_j)(oo) = 1, and set

        v_1 = (X_1 + X_2)/X_0,
        v_2 = (X_2 + X_3)/X_0,
        v_3 = (X_3 + X_1)/X_0,

    determined by

        div(v_1) = pp + qq - oo - rr,
        div(v_2) = qq + rr - oo - pp,
        div(v_3) = pp + rr - oo - qq,

    such that (v_i/v_j)(oo) = 1.

    A common normalization of the (u_i) and (v_i) is
    determined by the identities:

        u_1 = v_3 - v_2 = -a/v_1,
        u_2 = v_1 - v_3 = -b/v_2,
        u_3 = v_2 - v_1 = -c/v_3,

    which allows the determination of a, b, and c.

    Thus we begin with the determination of (v_i)
    and compute compatible (u_i).
    */
    // Compute the Riemann-Roch spaces:
    V1, m1 := RiemannRochSpace(oo + rr - pp - qq); assert Dimension(V1) eq 1;
    V2, m2 := RiemannRochSpace(oo + pp - qq - rr); assert Dimension(V2) eq 1;
    V3, m3 := RiemannRochSpace(oo + qq - pp - rr); assert Dimension(V3) eq 1;
    // Define v_i:
    v1 := m1(V1.1); v2 := m2(V2.1); v3 := m3(V3.1);
    // Renormalze:
    v2 *:= Evaluate(v1/v2,oo);
    v3 *:= Evaluate(v1/v3,oo);
    // Define u_i:
    u1 := v3 - v2; u2 := v1 - v3; u3 := v2 - v1;
    // Define x_i:
    x1 := (u1 + v1)/2;
    x2 := (u2 + v2)/2;
    x3 := (u3 + v3)/2;
    // Renormalze:
    x2 *:= Evaluate(x1/x2,oo);
    x3 *:= Evaluate(x1/x3,oo);
    // Compute a, b, c:
    a := -Evaluate(u1*v1,oo); // or evaluate at any point
    b := -Evaluate(u2*v2,oo); // or evaluate at any point
    c := -Evaluate(u3*v3,oo); // or evaluate at any point
    J := EllipticCurve_Jacobi_NormalForm([a,b,c]);
    m := map< C->J | [1,x1,x2,x3] >;
    return J, m;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Jacobi model transformations
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Jacobi_NormalForm(E::CrvEll,P::PtEll,Q::PtEll) -> Crv, MapSch
    {An elliptic curve in Jacobi normal form:
    aX0^2 + X1^2 = X2^2,
    bX0^2 + X2^2 = X3^2,
    cX0^2 + X3^2 = X1^2,
    where a + b + c = 0, with identity (0:1:1:1), given an elliptic
    curve E and 2-torsion points P and Q, which map to (0:-1:1:1) and
    (0:1:-1:1).}

    require Scheme(P) eq E : "Argument 2 must be a point on argument 1.";
    require Scheme(Q) eq E : "Argument 3 must be a point on argument 1.";
    K := BaseField(E);
    require P in E(K) : "Argument 2 must be a rational point of argument 1.";
    require Q in E(K) : "Argument 2 must be a rational point of argument 1.";
    O := E!0; R := P + Q;
    oo := Place(O); // O -> ( 0 : 1 : 1 : 1 )
    pp := Place(P); // P -> ( 0 :-1 : 1 : 1 )
    qq := Place(Q); // Q -> ( 0 : 1 :-1 : 1 )
    rr := Place(R); // R -> ( 0 : 1 : 1 :-1 )
    return EllipticCurve_Jacobi_NormalForm_Constructor(E,oo,pp,qq,rr);
end intrinsic;

intrinsic EllipticCurve_Jacobi_NormalForm(C::Crv,S::[Pt]) -> Crv, MapSch
    {An elliptic curve in Jacobi model:
        aX0^2 + X1^2 = X2^2,
        bX0^2 + X2^2 = X3^2,
        cX0^2 + X3^2 = X1^2,
    where a + b + c = 0, with identity (0:1:1:1), given an genus 1 curve C,
    base point O, and 2-torsion points P, Q, and R which map to (0:-1:1:1),
    (0:1:-1:1), and (0:1:1:-1).}

    require #S eq 4 : "Argument 2 must be a sequence of 4 points.";
    O, P, Q, R := Explode(S);
    K := BaseField(C);
    require Scheme(O) eq C : "Argument 2 must be a sequence of points on argument 1.";
    require O in C(K) : "Argument 2 must be a sequence of rational points of argument 1.";
    oo := Place(O); // O -> ( 0 : 1 : 1 : 1 )
    pp := Place(P); // P -> ( 0 :-1 : 1 : 1 )
    qq := Place(Q); // Q -> ( 0 : 1 :-1 : 1 )
    rr := Place(R); // R -> ( 0 : 1 : 1 :-1 )
    return EllipticCurve_Jacobi_NormalForm_Constructor(C,oo,pp,qq,rr);
end intrinsic;

intrinsic EllipticCurve_Jacobi_NormalForm(C::Crv,S::[PlcCrvElt]) -> Crv, MapSch
    {An elliptic curve in Jacobi normal form:
        aX0^2 + X1^2 = X2^2,
        bX0^2 + X2^2 = X3^2,
        cX0^2 + X3^2 = X1^2,
    where a + b + c = 0, with identity (0:1:1:1), given an genus 1 curve C,
    base point O, and 2-torsion points P, Q, and R which map to (0:-1:1:1),
    (0:1:-1:1), and (0:1:1:-1).}

    require #S eq 4 and &and[ Degree(pp) eq 1 : pp in S ] :
        "Argument 2 must be a sequence of 4 places of degree 1.";
    oo, pp, qq, rr := Explode(S);
    K := BaseField(C);
    require Curve(oo) eq C : "Argument 2 must be a sequence of places on argument 1.";
    // oo -> ( 0 : 1 : 1 : 1 )
    // pp -> ( 0 :-1 : 1 : 1 )
    // qq -> ( 0 : 1 :-1 : 1 )
    // rr -> ( 0 : 1 : 1 :-1 )
    return EllipticCurve_Jacobi_NormalForm_Constructor(C,oo,pp,qq,rr);
end intrinsic;

intrinsic EllipticCurve_Jacobi_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    require IsUnit(BaseRing(E)!2):
        "Argument 1 must be defined over a field of characteristic different from 2.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "(Mu_2 x Z/2Z)-normal form":
        r := Explode(EllipticModelInvariants(E));
        J := EllipticCurve_Jacobi_NormalForm(PP,[1-16/r,-1,16/r]);
        B_E_J := [X1-X3, 2*(X0+X2), X1+X3, 2*(X0-X2)];
        B_J_E := [X1+X3, 2*(X0+X2), X1-X3, 2*(X2-X0)];
        return J, map< E->J | B_E_J, B_J_E >;
    when "Split (mu_2 x Z/2Z)-normal form":
        c := Explode(EllipticModelInvariants(E));
        abc := [1,(c^4-16)/16, -c^4/16];
        J := EllipticCurve_Jacobi_NormalForm(PP,abc);
        B_E_J := [ 4*(X1 - X3), 2*c*(X0 - X2), 2*c*(X0 + X2), c^2*(X1 + X3) ];
        B_J_E := [ 2*c*(X1 + X2), c^2*X0 + 4*X3, -2*c*(X1 - X2), -c^2*X0 + 4*X3 ];
        return J, map< E->J | B_E_J, B_J_E >;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in (mu_2 x Z/2Z)-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Mu2xC2_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Split (mu_2 x Z/2Z)-normal form":
        return false;
    when "Jacobi normal form":
        a,b,c := Explode(EllipticModelInvariants(E));
        r := 16/c; s := -4*(b + 1)/c;
        require b eq -1:
            "Argument must be an untwisted Jacobi normal form (b = -1)";
        return false;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Mu4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Mu_4 normal form":
        return E, IdentityMorphism(E);
    when "Semisplit mu_4 normal form":
        s := Explode(E`EllipticModelInvariants); b := 1/s^2;
        C := EllipticCurve_Mu4_NormalForm(PP,b);
        return C, map< E->C | [X0,X1,s*X2,X3],[X0,X1,1/s*X2,X3] >;
    when "Split mu_4 normal form":
        D, iso_E_D := EllipticCurve_Semisplit_Mu4_NormalForm(E);
        C, iso_D_C := EllipticCurve_Mu4_NormalForm(D);
        return C, iso_E_D * iso_D_C;
    when "Edwards normal form":
        d, a := Explode(E`EllipticModelInvariants);
        require a eq -1: "Argument must be a -1-twist of an Edwards curve.";
        r := d/(16*a);
        C := EllipticCurve_Mu4_NormalForm(PP,r);
        B1 := [ X0, X1+X2, 4*X3, -X1+X2 ];
        B2 := [ 4*X0, 2*(X1-X3), 2*(X1+X3), X2 ];
        return C, map< E->C | B1, B2 >;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in semisplit mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Semisplit_Mu4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Semisplit mu_4 normal form":
        return E, IdentityMorphism(E);
    when "Split mu_4 normal form":
        c := Explode(E`EllipticModelInvariants); s := c^4;
        C := EllipticCurve_Semisplit_Mu4_NormalForm(PP,s);
        return C, map< E->C | [X0,c*X1,X2,c*X3],[c*X0,X1,c*X2,X3] >;
    when "Split Z/4Z-normal form":
        u := Explode(E`EllipticModelInvariants);
        C := EllipticCurve_Semisplit_Mu4_NormalForm(PP,(u + 1/u)^2);
        BB_E_C := [
            [ X0*X1 - u^2*X2*X3, X1^2 - u^2*X3^2, -u*X1*X2 + u*X0*X3, X0^2 - u^2*X2^2 ],
            [ X0*X2 + u*X3^2, X1*X2 - u^2*X0*X3, -u*X2^2 - u^2*X1*X3, -u*X0*X1 + u*X2*X3 ],
            [ u*(X1*X2 - X0*X3), u^2*X0^2 - X2^2, u^2*X0*X1 - X2*X3, -u^2*X1^2 + X3^2 ],
            [ u*X2^2 + X1*X3, -u*(X0*X1 - X2*X3), u*(u*X0*X2 + X3^2), -u^2*X1*X2 + X0*X3 ]
            ];
        BB_C_E := [
            [ X0*X1 - X2*X3, (u^2+1)/u^2*X0*X2 + X3^2, -1/u*X1*X2 - u*X0*X3, -(u^2+1)/u*X2^2 - u*X1*X3 ],
            [ (u^2+1)*X0*X2 + X3^2, X0*X3 + X1*X2, -(u^2+1)/u*X2^2 - u*X1*X3, -u*X0*X1 + 1/u*X2*X3 ],
            [ u^2*X1*X2 + X0*X3, (u^2+1)*X2^2 + X1*X3, -u*(X0*X1 - X2*X3), -u*((u^2+1)*X0*X2 + X3^2) ],
            [ (u^2+1)*X2^2 + X1*X3, X0*X1 - u^2*X2*X3, -(u^2+1)/u*X0*X2 - u*X3^2, -u*(X1*X2 + X0*X3) ] ];
        return C, map< E->C | BB_E_C, BB_C_E >;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in split mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Split_Mu4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Split mu_4 normal form":
        return E, IdentityMorphism(E);
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in twisted mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Mu4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Mu_4 normal form":
        return E, IdentityMorphism(E);
    when "Semisplit mu_4 normal form":
        return EllipticCurve_Mu4_NormalForm(E);
    when "Split mu_4 normal form":
        return EllipticCurve_Mu4_NormalForm(E);
    when "Twisted mu_4 normal form":
        return E, IdentityMorphism(E);
    when "Twisted semisplit mu_4 normal form":
        s, a := Explode(E`EllipticModelInvariants); b := 1/s^2;
        C := EllipticCurve_Twisted_Mu4_NormalForm(PP,b,a);
        return C, map< E->C | [X0,X1,s*X2,X3],[X0,X1,1/s*X2,X3] >;
    when "Twisted split mu_4 normal form":
        D, iso_E_D := EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(E);
        C, iso_D_C := EllipticCurve_Twisted_Mu4_NormalForm(D);
        return C, iso_E_D * iso_D_C;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in twisted semisplit mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Semisplit mu_4 normal form":
        return E, IdentityMorphism(E);
    when "Split mu_4 normal form":
        return EllipticCurve_Semisplit_Mu4_NormalForm(E);
    when "Twisted semisplit mu_4 normal form":
        return E, IdentityMorphism(E);
    when "Twisted split mu_4 normal form":
        c, a := Explode(E`EllipticModelInvariants); s := c^4;
        C := EllipticCurve_Twisted_Semisplit_Mu4_NormalForm(PP,s,a);
        return C, map< E->C | [X0,c*X1,X2,c*X3],[c*X0,X1,c*X2,X3] >;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in twisted split mu_4 normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Twisted_Split_Mu4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0,X1,X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0,X1,X2,X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Split mu_4 normal form":
        return E, IdentityMorphism(E);
    when "Twisted split mu_4 normal form":
        return E, IdentityMorphism(E);
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curve Z/4Z-normal form constructors
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function EllipticCurve_C4_NormalForm_Constructor_Char2(C,oo,tt,ss,rr)
    // Given places (identity) oo, (2-torsion) pp, and (4-torsion) qq and rr,
    // construct the binary level 4 canonical model
    //
    //    (X0 + X1 + X2 + X3)^2 = e*X0*X2 = e*X1*X3 [X0*X2 = X1*X3]
    //
    // with embedding :
    //                      (X_0 X_1 X_2 X_3)
    // oo := Place(O) : O = ( 1 : 0 : 0 : 1 )
    // tt := Place(T) : T = ( 1 : 1 : 0 : 0 )
    // ss := Place(S) : S = ( 0 : 1 : 1 : 0 ) = 2T
    // rr := Place(R) : R = ( 0 : 0 : 1 : 1 ) = -T
    //
    // given by the embedding ( 1 :x_1:x_2:x_3) with x_2 = x_1*x_3, such that:
    //
    //            div(x_1) = 2(O) - 2(S),
    //            div(x_3) = 2(T) - 2(R),
    //
    // with normalization:
    //
    //            div(x_1+1) = (T) + (R) - 2(S),
    //            div(x_3+1) = (O) + (S) - 2(R).
    //
    K := BaseRing(C); assert Characteristic(K) eq 2;
    PP := AmbientSpace(C);
    if Type(PP) ne Prj or Dimension(PP) ne 3 then
        PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    end if;
    //
    V1, m1 := RiemannRochSpace(2*(ss-oo)); assert Dimension(V1) eq 1;
    x1 := m1(V1.1); // = X1/X0
    x1 *:= 1/Evaluate(x1,tt);
    //
    V3, m3 := RiemannRochSpace(2*(rr-tt)); assert Dimension(V3) eq 1;
    x3 := m3(V3.1); // = X3/X0
    x3 *:= 1/Evaluate(x3,oo);
    //
    x2 := x1*x3;
    // The constant e can be determined by evaluation at any point:
    e := Evaluate(((1-x1)*(1-x3))^2/x2,oo);
    E := EllipticCurve_C4_NormalForm(PP,e);
    // This gives an elliptic curve in
    //    (X0 + X1 + X2 + X3)^2 = e*X0*X2 = e*X1*X3 [X0*X2 = X1*X3]
    m := map< C->E | [1,x1,x2,x3] >;
    return E, m;
end function;

function EllipticCurve_C4_NormalForm_Constructor_Char0(C,oo,tt,ss,rr)
    // Given places (identity) oo, (4-torsion) tt, (2-torsion) ss, and
    // rr = [-1]^*(tt) , construct the binary level 4 canonical model
    //
    //    (X0 - X1 + X2 - X3)^2 = (e+8)*X0*X2 = (e+8)*X1*X3 [X0*X2 = X1*X3]
    //
    // with embedding :
    //                      (X_0 X_1 X_2 X_3)
    // oo := Place(O) : O = ( 1 : 0 : 0 : 1 )
    // tt := Place(T) : T = ( 1 : 1 : 0 : 0 )
    // ss := Place(S) : S = ( 0 :-1 : 1 : 0 ) = 2T
    // rr := Place(R) : R = ( 0 : 0 :-1 : 1 ) = -T
    //
    // given by the embedding ( 1 :x_1:x_2:x_3) with x_2 = x_1*x_3, such that:
    //
    //            div(x_1) = 2(O) - 2(S),
    //            div(x_3) = 2(T) - 2(R),
    //
    // with normalization:
    //
    //            div(x_1-1) = (T) + (R) - 2(S),
    //            div(x_3-1) = (O) + (S) - 2(R).
    //
    K := BaseRing(C);
    //
    V1, m1 := RiemannRochSpace(2*(ss-oo)); assert Dimension(V1) eq 1;
    x1 := m1(V1.1); // = X1/X0
    x1 *:= 1/Evaluate(x1,tt);
    //
    V3, m3 := RiemannRochSpace(2*(rr-tt)); assert Dimension(V3) eq 1;
    x3 := m3(V3.1); // = X3/X0
    x3 *:= 1/Evaluate(x3,oo);
    //
    x2 := x1*x3;
    //
    PP := AmbientSpace(C);
    if Type(PP) ne Prj or Dimension(PP) ne 3 then
        PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
    end if;
    // The constant e can be determined by evaluation at any point:
    e := Evaluate((1-x1+x2-x3)^2/x2,oo);
    E := EllipticCurve_C4_NormalForm(e-8);
    m := map< C->E | [1,x1,x2,x3] >;
    return E, m;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_C4_NormalForm(E::Crv,TorsPnts::SeqEnum[Pt]) -> Crv, MapSch
    {Given a genus 1 curve with given 4-torsion subgroup [O,T,2T,-T], returns
    an elliptic curve in Z/4Z-normal form in PP (= PP^3), given by
    (X0 - X1 + X2 - X3)^2 = (e + 8)*X0*X2, X0*X2 = X1*X3, sending O to the
    identity (1:0:0:1) and T to (1:1:0:0), followed by the isomorphism.}
    require #TorsPnts eq 4 : "Argument 2 must be a sequence of 4 points.";
    O, T, S, R := Explode(TorsPnts);
    require E eq Scheme(O) : "Argument 2 must be rational points of argument 1.";
    /*
    O := Identity(E);
    S := 2*T;
    require S ne O and 2*S eq O : "Argument 2 must be a 4-torsion point.";
    R := -T;
    */
    oo := Place(O);
    tt := Place(T);
    ss := Place(S);
    rr := Place(R);
    if Characteristic(BaseRing(E)) eq 2 then
        return EllipticCurve_C4_NormalForm_Constructor_Char2(E,oo,tt,ss,rr);
    else
        return EllipticCurve_C4_NormalForm_Constructor_Char0(E,oo,tt,ss,rr);
    end if;
end intrinsic;

intrinsic EllipticCurve_C4_NormalForm(E::Crv,T::Pt) -> Crv, MapSch
    {}
    K := BaseRing(E);
    require E eq Scheme(T) and Ring(Parent(T)) cmpeq K :
        "Argument 2 must be a rational point of argument 1.";
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    if assigned E`EllipticModelType then
        PP := AmbientSpace(E);
        if Dimension(PP) eq 2 then
            X0, X1, X2 := Explode([ PP.i : i in [1..3] ]);
        elif Dimension(PP) eq 3 then
            X0, X1, X2, X3 := Explode([ PP.i : i in [1..4] ]);
        end if;
        case E`EllipticModelType:
        when "Z/4Z-normal form":
            if T eq E![1,1,0,0] then
                return E, IdentityMorphism(E);
            elif T eq E![0,0,1,1] then
                return E, InverseMorphism(E);
            end if;
            require false :
                "The torsion point on the Z/4Z-normal form should be T = (1:1:0:0) or (0:0:1:1).";
        when "Semisplit Z/4Z-normal form":
            C, iso_E_C := EllipticCurve_C4_NormalForm(E);
            if T eq E![1,1,0,0] then
                return C, iso_E_C;
            elif T eq E![0,0,-1,1] then
                return C, InverseMorphism(E) * iso_E_C;
            end if;
            require false :
                "The torsion point on the semisplit Z/4Z-normal form " *
                "should be T = (1:1:0:0) or (0:0:-1:1).";
        when "Split Z/4Z-normal form":
            C, iso_E_C := EllipticCurve_C4_NormalForm(E);
            u := Explode(E`EllipticModelInvariants);
            if T eq E![u,-1,-1,u] then
                return C, iso_E_C;
            elif T eq E![1,-u,-u,1] then
                return C, InverseMorphism(E) * iso_E_C;
            end if;
            require false :
                "The torsion point on the semisplit Z/4Z-normal form " *
                "should be T = (u:-1:-1:u) or (1:-u:-u:1).";
        end case;
    end if;
    // Fall back to a generic constructor
    O := Identity(E);
    S := 2*T;
    require S ne O and 2*S eq O : "Argument 2 must be a 4-torsion point.";
    R := -T;
    oo := Place(O);
    tt := Place(T);
    ss := Place(S);
    rr := Place(R);
    if Characteristic(BaseRing(E)) eq 2 then
        return EllipticCurve_C4_NormalForm_Constructor_Char2(E,oo,tt,ss,rr);
    else
        return EllipticCurve_C4_NormalForm_Constructor_Char0(E,oo,tt,ss,rr);
    end if;
end intrinsic;

intrinsic EllipticCurve_C4_NormalForm(E::Crv) -> Crv, MapSch
    {Given an elliptic curve model in a prescribed normal form with
    4-torsion point, return the elliptic curve in Z/4Z-normal form
    together with the isomorphism.}
    K := BaseRing(E);
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0, X1, X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0, X1, X2, X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Edwards normal form":
        d, a := Explode(E`EllipticModelInvariants);
        require a eq 1: "Argument must be an untwisted Edwards curve.";
        e := -8*(d+1)/(d-1);
        C := EllipticCurve_C4_NormalForm(PP,e);
        B := [ X0 + X1 + X2 + X3, X0 + X1 - X2 - X3, X0 - X1 - X2 + X3, X0 - X1 + X2 - X3 ];
        return C, map< E->C | B, B >;
    when "Split mu_4 normal form":
        D, iso_E_D := EllipticCurve_Semisplit_C4_NormalForm(E);
        C, iso_D_C := EllipticCurve_C4_NormalForm(D);
        return C, iso_E_D * iso_D_C;
    when "Z/4Z-normal form":
        return E, IdentityMorphism(E);
    when "Semisplit Z/4Z-normal form":
        c := Explode(E`EllipticModelInvariants);
        e := (c^2+16)/c;
        C := EllipticCurve_C4_NormalForm(PP,e);
        iso_E_C := map< E->C |
            [
            c*X0 - 2*(X0 + X1 + X2 + X3),
            c*X1 - 2*(X0 + X1 - X2 - X3),
            -c*X2 + 2*(X0 - X1 + X2 - X3),
            c*X3 - 2*(X0 - X1 - X2 + X3)
            ],
            [
            c*X0 + 2*(X0 + X1 - X2 + X3),
            c*X1 + 2*(X0 + X1 + X2 - X3),
            -c*X2 + 2*(X0 - X1 - X2 - X3),
            c*X3 + 2*(X0 - X1 + X2 + X3)
            ] >;
        return C, iso_E_C;
    when "Split Z/4Z-normal form":
        D, iso_E_D := EllipticCurve_Semisplit_C4_NormalForm(E);
        C, iso_D_C := EllipticCurve_C4_NormalForm(D);
        return C, iso_E_D * iso_D_C;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

intrinsic EllipticCurve_Twisted_C4_NormalForm(E::Crv) -> Crv, MapSch
    {Given an elliptic curve model in a twisted of a prescribed normal form
    with 4-torsion point, return the elliptic curve in twisted Z/4Z-normal
    form together with the isomorphism.}
    K := BaseRing(E);
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0, X1, X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0, X1, X2, X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Edwards normal form":
        d, a := Explode(E`EllipticModelInvariants);
        if a eq 1 then
            return EllipticCurve_C4_NormalForm(E);
        else
            require false : "Not implemented.";
        end if;
    when "Split mu_4 normal form":
        return EllipticCurve_C4_NormalForm(E);
    when "Twisted split mu_4 normal form":
        c, a := Explode(EllipticModelInvariants(E));
        s := (c^4+4)/c^2;
        D := EllipticCurve_Twisted_Semisplit_C4_NormalForm(PP,s,a);
        assert Characteristic(K) eq 2;
        BB_E_D_1 := [[c*X0,X1+X3],[X1+X3,c*X2]];
        BB_E_D_2 := [[X0+X2+c*a*(X1+X3),c*(X3+a*(X1+X3))],[c*(X1+a*(X1+X3)),X0+X2+c*a*(X1+X3)]];
        BB_E_D := [ [ U[1]*V[1], U[2]*V[1], U[2]*V[2], U[1]*V[2] ] : U in BB_E_D_1, V in BB_E_D_2 ];
        BB_D_E := [ [
            X0*X1 + X2*X3,
            c*(X1^2 + a*(X1+X2)^2),
            (X0+c^2*(a*X1+X2))*X1 + (c^2*a*X2+X3)*X2,
            c*(X2^2 + a*(X1+X2)^2)
            ],[
            c*X0*X3,
            (X0+X1)^2 + c^2*a*(X0+X3)*X1,
            c*X1*X2,
            (X2+X3)^2 + c^2*a*(X1+X2)*X3
            ],[
            X1^2 + X2^2 + c^2*X1*X3,
            c*((a+1)*X0*X1 + c^2*a*(a+1)*X1^2 + c^2*a^2*X2^2 + a*X2*X3),
            X0^2 + c^2*X0*X2 + c^4*a^2*X1^2 + c^4*a*X1*X2 + c^4*a^2*X2^2 + X3^2,
            c*(a*X0*X1 + c^2*a^2*X1^2 + c^2*a*(a+1)*X2^2 + (a+1)*X2*X3)
            ],[
            c*X3^2,
            X1*X2 + X0*X3 + c^2*a*(X1+X2)*X3,
            c*X2^2,
            X1*X2 + X0*X3 + c^2*a*(X1+X2)*X3 + c^2*X2*X3] ];
        iso_E_D := map< E->D | BB_E_D, BB_D_E >;
        C, iso_D_C := EllipticCurve_Twisted_C4_NormalForm(D);
        return C, iso_E_D * iso_D_C;
    when "Z/4Z-normal form":
        return E, IdentityMorphism(E);
    when "Semisplit Z/4Z-normal form":
        return EllipticCurve_C4_NormalForm(E);
    when "Split Z/4Z-normal form":
        return EllipticCurve_C4_NormalForm(E);
    when "Twisted Z/4Z-normal form":
        return E, IdentityMorphism(E);
    when "Twisted semisplit Z/4Z-normal form":
        c, a := Explode(E`EllipticModelInvariants);
        e := (c^2+16)/c;
        C := EllipticCurve_Twisted_C4_NormalForm(PP,e,a);
        iso_E_C := map< E->C |
            [
            c*X0 - 2*(X0 + X1 + X2 + X3),
            c*X1 - 2*(X0 + X1 - X2 - X3),
            -c*X2 + 2*(X0 - X1 + X2 - X3),
            c*X3 - 2*(X0 - X1 - X2 + X3)
            ],
            [
            c*X0 + 2*(X0 + X1 - X2 + X3),
            c*X1 + 2*(X0 + X1 + X2 - X3),
            -c*X2 + 2*(X0 - X1 - X2 - X3),
            c*X3 + 2*(X0 - X1 + X2 + X3)
            ] >;
        return C, iso_E_C;
    when "Twisted split Z/4Z-normal form":
        D, iso_E_D := EllipticCurve_Twisted_Semisplit_C4_NormalForm(E);
        C, iso_D_C := EllipticCurve_Twisted_C4_NormalForm(D);
        return C, iso_E_D * iso_D_C;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in semisplit Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_Semisplit_C4_NormalForm(E::Crv,T::Pt,S::Pt) -> Crv, MapSch
    {}
    K := BaseRing(E);
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require E eq Scheme(T) and Ring(Parent(T)) eq K :
        "Argument 2 must be a rational point of argument 1.";
    require E eq Scheme(S) and Ring(Parent(S)) eq K :
        "Argument 3 must be a rational point of argument 1.";
    if Type(E) ne CrvEll then
        require IsEllipticCurve(E): "Argument must be an elliptic curve model.";
        require assigned E`EllipticModelType:
            "Argument 1 must be an elliptic curve in prescribed normal form.";
        PP := AmbientSpace(E);
        case E`EllipticModelType:
        when "Huff normal form":
            C, iso_E_C := EllipticCurve_Semisplit_C4_NormalForm(E);
            if T eq E![1,1,1] and S eq E![0,0,1] then
                return C, iso_E_C;
            end if;
            require false : "The torsion points on the Huff normal form " *
                "should be T = (1:1:1) and S = (0:1:0).";
        when "Semisplit Z/4Z-normal form":
            if T eq E![1,1,0,0] and S eq E![-1,0,0,1] then
                return E, IdentityMorphism(E);
            elif T eq E![0,0,-1,1] and S eq E![-1,0,0,1] then
                return E, InverseMorphism(E);
            end if;
            require false : "The torsion points on the semisplit Z/4Z-normal form " *
                "should be T = (1:1:0:0) or (0:0:-1:1) and S = (-1:0:0:1).";
        when "Split Z/4Z-normal form":
            D, iso_E_D := EllipticCurve_Semisplit_C4_NormalForm(E);
            u := Explode(E`EllipticModelInvariants);
            if T eq E![u,-1,-1,u] and S eq E![1,-1,-u,u] then
                return D, iso_E_D;
            elif T eq E![1,-u,-u,1] and S eq E![1,-1,-u,u] then
                return D, InverseMorphism(E) * iso_E_D;
            end if;
            require false : "The torsion points on the split Z/4Z-normal form " *
                "should be T = (u:-1:-1:u) or (1:-u:-u:1) and S = (1:-1:-u:u).";
        end case;
    end if;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

intrinsic EllipticCurve_Semisplit_C4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    K := BaseRing(E);
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0, X1, X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0, X1, X2, X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    when "Huff normal form":
        a, b := Explode(E`EllipticModelInvariants); u := a/b;
        B_E_C := [
            [ X0^2 + X0*X2, X0*X1 + X1*X2, X0*X1 - X1*X2, X0^2 - X0*X2 ],
            [
            X0*X1 + X1*X2 - u*(X0*X2 + X2^2),
            X1^2 + X0*X2 - u*(X0*X1 + X1*X2),
            X1^2 - X0*X2 + u*(X0*X1 - X1*X2),
            X0*X1 - X1*X2 - u*(X0*X2 - X2^2)
            ]
            ];
        PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
        C := EllipticCurve_Semisplit_C4_NormalForm(PP,4*u);
        B_C_E := [ X0 + X3, X1 + X2, X0 - X3 ];
        return C, map< E->C | B_E_C, B_C_E >;
    when "Semisplit Z/4Z-normal form":
        return E, IdentityMorphism(E);
    when "Split Z/4Z-normal form":
        u := E`EllipticModelInvariants[1];
        c := -(u^4 + 6*u^2 + 1)/(u^3 + u);
        D := EllipticCurve_Semisplit_C4_NormalForm(PP,c);
        iso_E_D := map< E->D |
            [ X0+u*X2, u*X1+X3, -(u*X0+X2), X1+u*X3 ],
            [-(X0+u*X2), u*X1-X3, u*X0+X2, -X1+u*X3 ] >;
        return D, iso_E_D;
    when "Split mu_4 normal form":
        c := E`EllipticModelInvariants[1];
        e := (c^4+4)/c^2;
        D := EllipticCurve_Semisplit_C4_NormalForm(e);
        BB_E_D := [
            [ c^2*X0*X1, c*X1*(X1 - X3), (X0 - X2)*(X1 - X3), c*X0*(X0 - X2) ],
            [ c*X1*(X1 + X3), c^2*X1*X2, c*(X0 - X2)*X2, (X0 - X2)*(X1 + X3) ],
            [ (X0 + X2)*(X1 + X3), c*(X0 + X2)*X2, c^2*X2*X3, c*(X1 + X3)*X3 ],
            [ c*X0*(X0 + X2), (X0 + X2)*(X1 - X3), c*(X1 - X3)*X3, c^2*X0*X3 ]
            ];
        BB_D_E := [
            [ (c*X0 - 2/c*X2)*X3, c^2*X0*X2 - X2^2 + X3^2, (c*X1 + 2/c*X3)*X2, X2^2 + X3^2 ],
            [ X1^2 - X2^2 + c^2*X1*X3, (c*X0 - 2/c*X2)*X1, X1^2 + X2^2, (2/c*X1 + c*X3)*X2 ],
            [ X0*X1 + X2*X3, (c*X1 + 2/c*X3)*X1, X0*X1 - c^2*X1*X2 - X2*X3, -(c*X2 - 2/c*X0)*X2 ],
            [ (2/c*X1 + c*X3)*X3, X1*X2 + X0*X3, -(c*X2 - 2/c*X0)*X2, -X1*X2 + X0*X3 - c^2*X2*X3 ]
            ];
        iso_E_D := map< E->D | BB_E_D, BB_D_E >;
        return D, iso_E_D;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

intrinsic EllipticCurve_Twisted_Semisplit_C4_NormalForm(E::Crv) -> Crv, MapSch
    {}
    K := BaseRing(E);
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0, X1, X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0, X1, X2, X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    case E`EllipticModelType:
    /*
    when "Huff normal form":
        a, b := Explode(E`EllipticModelInvariants); u := a/b;
        B_E_C := [
            [ X0^2 + X0*X2, X0*X1 + X1*X2, X0*X1 - X1*X2, X0^2 - X0*X2 ],
            [
            X0*X1 + X1*X2 - u*(X0*X2 + X2^2),
            X1^2 + X0*X2 - u*(X0*X1 + X1*X2),
            X1^2 - X0*X2 + u*(X0*X1 - X1*X2),
            X0*X1 - X1*X2 - u*(X0*X2 - X2^2)
            ]
            ];
        PP<X0,X1,X2,X3> := ProjectiveSpace(K,3);
        C := EllipticCurve_Semisplit_C4_NormalForm(PP,4*u);
        B_C_E := [ X0 + X3, X1 + X2, X0 - X3 ];
        return C, map< E->C | B_E_C, B_C_E >;
    */
    when "Semisplit Z/4Z-normal form":
        return E, IdentityMorphism(E);
    when "Twisted semisplit Z/4Z-normal form":
        return E, IdentityMorphism(E);
    when "Split Z/4Z-normal form":
        return EllipticCurve_Semisplit_C4_NormalForm(E);
    when "Twisted split Z/4Z-normal form":
        u := E`EllipticModelInvariants[1];
        c := -(u^4 + 6*u^2 + 1)/(u^3 + u);
        D := EllipticCurve_Semisplit_C4_NormalForm(PP,c);
        iso_E_D := map< E->D |
            [ X0+u*X2, u*X1+X3, -(u*X0+X2), X1+u*X3 ],
            [-(X0+u*X2), u*X1-X3, u*X0+X2, -X1+u*X3 ] >;
        return D, iso_E_D;
    when "Split mu_4 normal form":
        return EllipticCurve_Semisplit_C4_NormalForm(E);
    when "Twisted split mu_4 normal form":
        c,a := Explode(EllipticModelInvariants(E));
        e := (c^4+4)/c^2;
        D := EllipticCurve_Twisted_Semisplit_C4_NormalForm(e,a);
        /*
        BB_E_D := [
            [ c^2*X0*X1, c*X1*(X1 - X3), (X0 - X2)*(X1 - X3), c*X0*(X0 - X2) ],
            [ c*X1*(X1 + X3), c^2*X1*X2, c*(X0 - X2)*X2, (X0 - X2)*(X1 + X3) ],
            [ (X0 + X2)*(X1 + X3), c*(X0 + X2)*X2, c^2*X2*X3, c*(X1 + X3)*X3 ],
            [ c*X0*(X0 + X2), (X0 + X2)*(X1 - X3), c*(X1 - X3)*X3, c^2*X0*X3 ]
            ];
        BB_D_E := [
            [ (c*X0 - 2/c*X2)*X3, c^2*X0*X2 - X2^2 + X3^2, (c*X1 + 2/c*X3)*X2, X2^2 + X3^2 ],
            [ X1^2 - X2^2 + c^2*X1*X3, (c*X0 - 2/c*X2)*X1, X1^2 + X2^2, (2/c*X1 + c*X3)*X2 ],
            [ X0*X1 + X2*X3, (c*X1 + 2/c*X3)*X1, X0*X1 - c^2*X1*X2 - X2*X3, -(c*X2 - 2/c*X0)*X2 ],
            [ (2/c*X1 + c*X3)*X3, X1*X2 + X0*X3, -(c*X2 - 2/c*X0)*X2, -X1*X2 + X0*X3 - c^2*X2*X3 ]
            ];
        iso_E_D := map< E->D | BB_E_D, BB_D_E >;
        */
        return D; //, iso_E_D;
    end case;
    require false:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Split Z/4Z-normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
// Elliptic curves in Kummer oriented product normal form
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic EllipticCurve_MontgomeryOriented_KummerProduct(E::Crv,P::Pt) -> Crv, MapSch
    {}
    K := BaseRing(E);
    require IsEllipticCurve(E): "Argument 1 must be an elliptic curve model.";
    require assigned E`EllipticModelType:
        "Argument 1 must be an elliptic curve in prescribed normal form.";
    PP := AmbientSpace(E);
    if Dimension(PP) eq 2 then
        X0, X1, X2 := Explode([ PP.i : i in [1..3] ]);
    elif Dimension(PP) eq 3 then
        X0, X1, X2, X3 := Explode([ PP.i : i in [1..4] ]);
    end if;
    K := BaseField(E);
    ModelType := EllipticModelType(E);
    ModelInvs := EllipticModelInvariants(E);
    if Ring(Parent(P)) cmpne K then
        K := Ring(Parent(P));
        E := BaseExtend(E,K);
        PP<X0,X1,X2,X3> := Ambient(E);
    end if;
    // For each model type, we need to define the defining
    // polynomials BB_1 for the Kummer morphism pi such that
    // pi(O) = oo = (1:0), pi(T) = (0:1), pi(2*T) = (1:1),
    // for a 4-torsion point T, as well as defining polynomials
    // BB_2 for pi(P+Q).
    MorphismInverse := false;
    // The maps below are given by (pi(Q),pi(Q+P)), but
    // we want pi(Q-P) in the second coordinate.
    Y0,Y1,Y2,Y3 := Explode(Eltseq(-P));
    case ModelType:
    when "Huff normal form":
        require false: "Not implemented for Huff normal form.";
    when "Edwards normal form":
        // Note this type includes all twisted Edwards models
        d,a := Explode(ModelInvs);
        // See note below about normalization of Kummer morphism.
        if Y1 ne 0 or Y3 ne 0 then
            t0, t1 := Explode([Y1+Y3,Y1-Y3]);
        else
            t0, t1 := Explode([Y0+Y2,Y0-Y2]);
        end if;
        e := -8*(d+1)/(d-1);
        // This gives the wrong map to PP^1 relative to Z/4Z-normal form:
        AA_1 := [[X0,X2],[X1,X3]];
        AA_2 := [[X2*Y1-X1*Y2,X0*Y3-X3*Y0],[X0*Y0-d*X3*Y3,X2*Y2-a*X1*Y1]];
        // need to compose with the map (U0,U1) |-> (U0+U1,U0-U1), giving
        BB_1 := [[S[1]+S[2],S[1]-S[2]] : S in AA_1];
        BB_2 := [[S[1]+S[2],S[1]-S[2]] : S in AA_2];
        BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
        K2 := EllipticCurve_MontgomeryOriented_C4_KummerProduct(e,[t0,t1]);
        if a ne 1 then
            iso_E_K2 := map< E->K2 | BB >;
        else
            P1xP1<U0,U1,V0,V1> := AmbientSpace(K2);
            BB_inv := [[
                (U0+U1)*(Y0*(U0-U1)*(V0+V1)-Y2*(U0+U1)*(V0-V1)),
                (U0+U1)*(Y3*(U0+U1)*(V0+V1)-Y1*(U0-U1)*(V0-V1)),
                (U0-U1)*(Y0*(U0-U1)*(V0+V1)-Y2*(U0+U1)*(V0-V1)),
                (U0-U1)*(Y3*(U0+U1)*(V0+V1)-Y1*(U0-U1)*(V0-V1))
                ]];
            iso_E_K2 := map< E->K2 | BB, BB_inv >;
        end if;
    when "Z/4Z-normal form":
        e := Explode(ModelInvs);
        t0, t1 := Explode([Y3,Y2]);
        if t0 eq 0 and t1 eq 0 then
        t0, t1 := Explode([Y0,Y1]);
        end if;
        BB_1 := [[X0,X1],[X3,X2]];
        BB_2 := [[
            (e + 4)*(X1*Y2+X3*Y0)
            + 2*(X2*(Y0-Y3) + X3*(Y1-Y2) + (X0+X2)*Y2 + (X1+X3)*Y3 + (X0-X1)*(Y0-Y1)),
            (e + 4)*(X0*Y1+X2*Y3)
            + 2*(X0*(Y0-Y3) + X1*(Y1-Y2) + (X0+X2)*Y2 + (X1+X3)*Y3 + (X2-X3)*(Y0-Y1)) ],
            [ X0*Y3 - X1*Y2 + X2*Y1 - X3*Y0, -X0*Y1 + X1*Y0 - X2*Y3 + X3*Y2]];
        BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
        K2 := EllipticCurve_MontgomeryOriented_C4_KummerProduct(e,[t0,t1]);
        P1xP1<U0,U1,V0,V1> := AmbientSpace(K2);
        BB_inv := [[
            U0*(Y2*U0*V0 + Y0*U0*V1 - Y3*U1*V0 - Y1*U1*V1),
            U1*(Y2*U0*V0 + Y0*U0*V1 - Y3*U1*V0 - Y1*U1*V1),
            U1*(Y1*U0*V0 + Y3*U0*V1 - Y0*U1*V0 - Y2*U1*V1),
            U0*(Y1*U0*V0 + Y3*U0*V1 - Y0*U1*V0 - Y2*U1*V1)
            ]];
        iso_E_K2 := map< E->K2 | BB, BB_inv >;
    when "Semisplit Z/4Z-normal form":
        c := Explode(ModelInvs);
        e := (c^2 + 16)/c;
        t0, t1 := Explode([Y0+Y3,Y1-Y2]);
        if t0 eq 0 and t1 eq 0 then
            t0, t1 := Explode([2*(Y1+Y2)+c*Y3,2*(Y0-Y3)-c*Y2]);
        end if;
        BB_1 := [[X0 + X3, X1 - X2], [2*(X1 + X2) + c*X3, 2*(X0 - X3) - c*X2]];
        BB_2 := [[
            c*(X3*Y0 - X1*Y2) + 2*(X1*Y0 - X0*Y1 - X3*Y2 + X2*Y3),
            c*(X0*Y1 - X2*Y3) - 2*(X3*Y0 + X2*Y1 - X1*Y2 - X0*Y3) ],
            [ X3*Y0 - X2*Y1 - X1*Y2 + X0*Y3, X1*Y0 + X0*Y1 - X3*Y2 - X2*Y3 ]];
        BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
        K2 := EllipticCurve_MontgomeryOriented_C4_KummerProduct(e,[t0,t1]);
        iso_E_K2 := map< E->K2 | BB >;
    when "Split Z/4Z-normal form":
        u := Explode(ModelInvs);
        s := (u^2+1)/u;
        c := -(u^4 + 6*u^2 + 1)/(u^3 + u);
        e := (c^2 + 16)/c;
        if Y0+Y1 ne 0 then
            t0, t1 := Explode([(Y0+Y1)+u*(Y2+Y3),u*(Y0+Y1)+Y2+Y3]);
        else
            t0 := s*(X0 - u*X2) - 2*(u*X1 - X3);
            t1 := 2*(X0 - u*X2) - s*(u*X1 - X3);
        end if;
        BB_1 := [[X0 + X1 + u*(X2 + X3), u*(X0 + X1) + X2 + X3],
            [s*(X0 - u*X2) - 2*(u*X1 - X3), 2*(X0 - u*X2) - s*(u*X1 - X3)]];
        BB_2 := [[
            s*(X0*Y1 + X2*Y3) + 2*(X1*Y2 + X3*Y0),
            2*(X0*Y1 + X2*Y3) + s*(X1*Y2 + X3*Y0)],[
            2*(X0*Y3 + X2*Y1) + s*(X1*Y0 + X3*Y2),
            s*(X0*Y3 + X2*Y1) + 2*(X1*Y0 + X3*Y2)]];
        BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
        K2 := EllipticCurve_MontgomeryOriented_C4_KummerProduct(e,[t0,t1]);
        iso_E_K2 := map< E->K2 | BB >;
    when "Mu_4 normal form":
        if Characteristic(K) eq 2 then
            r := Explode(ModelInvs);
            bool, s := IsSquare(1/r); assert bool;
            bool, t := IsSquare(s); assert bool;
            bool, c := IsSquare(t); assert bool;
            u := (t^2 + 4)/t;
            e := (u^2 + 16)/u;
            if Y0 ne 0 then
                t0, t1 := Explode([Y0,Y1+Y3]);
            else
                t0, t1 := Explode([Y1+Y3,Y2]);
            end if;
            BB_1 := [[X0,X1+X3],[X1-X3,X2]];
            BB_2 := [[X0*Y0+r*X2*Y2,X1*Y1+X3*Y3],[X3*Y1-X1*Y3,X0*Y2-X2*Y0]];
            BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
            K2 := EllipticCurve_MontgomeryOriented_C4_KummerProduct(e,[t0,t1]);
            P1xP1<U0,U1,V0,V1> := AmbientSpace(K2);
            BB_inv := [[
                (Y1 + Y3)*U0^2*V0,
                (Y0*U0^2 + Y2*U1^2)*V1 + c*Y1*U0*U1*V0,
                (Y1 + Y3)*U1^2*V0,
                (Y0*U0^2 + Y2*U1^2)*V1 + c*Y3*U0*U1*V0],
                [
                (Y1 + Y3)*U0^2*V1,
                (Y2*U0^2 + Y0*U1^2)*V0 + c*Y3*U0*U1*V1,
                (Y1 + Y3)*U1^2*V1,
                (Y2*U0^2 + Y0*U1^2)*V0 + c*Y1*U0*U1*V1]];
            K2 := Image(map< E->P1xP1 | BB >);
            iso_E_K2 := map< E->K2 | BB, BB_inv >;
        else
            r := Explode(ModelInvs);
            // bool, s := IsSquare(1/r); assert bool;
            // bool, c := IsSquare(s); assert bool;
            // bool, c := IsSquare(c); assert bool;
            // Not good reduction at 2:
            e := -8*(16*r + 1)/(16*r - 1);
            if 2*Y0+Y1+Y3 ne 0 then
                t0, t1 := Explode([2*Y0+Y1+Y3,2*Y0-Y1-Y3]);
            else
                t0, t1 := Explode([2*(Y1-Y3)+Y2,2*(Y1-Y3)-Y2]);
            end if;
            // This gives the wrong map to PP^1 relative to Z/4Z-normal form:
            AA_1 := [[X0,X1+X3],[X1-X3,X2]];
            AA_2 := [[X0*Y0+r*X2*Y2,X1*Y1+X3*Y3],[X3*Y1-X1*Y3,X0*Y2-X2*Y0]];
            // need to compose with the map (U0,U1) |-> (2U0+U1,2U0-V1), giving
            // the correctly normalized Kummer morphism:
            BB_1 := [[2*S[1]+S[2],2*S[1]-S[2]] : S in AA_1];
            BB_2 := [[2*S[1]+S[2],2*S[1]-S[2]] : S in AA_2];
            MorphismInverse := false;
            // This change of variables is an isomorphism between
            // the Z/4Z and Mu4 models for the Kummer line.
            BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
            K2 := EllipticCurve_MontgomeryOriented_C4_KummerProduct(e,[t0,t1]);
            iso_E_K2 := map< E->K2 | BB >;
        end if;
    when "Semisplit mu_4 normal form":
        /*
        s := Explode(ModelInvs);
        r := 1/s^2;
        bool, c := IsSquare(s); assert bool;
        bool, c := IsSquare(c); assert bool;
        if Y0 ne 0 then
            t0, t1 := Explode([Y0,Y1+Y3]);
        else
            t0, t1 := Explode([X1-X3,s*Y2]);
        end if;
        BB_1 := [[X0,X1+X3],[X1-X3,s*X2]];
        BB_2 := [[X0*Y0+X2*Y2,X1*Y1+X3*Y3],[X3*Y1-X1*Y3,s*(X0*Y2-X2*Y0)]];
        BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
        K2 := EllipticCurve_MontgomeryOriented_Mu4_KummerProduct(c,[t0,t1]);
        iso_E_K2 := map< E->K2 | BB >;
        */
        C0, iso_E_C0 := EllipticCurve_Mu4_NormalForm(E);
        P0 := iso_E_C0(P);
        K2, iso_C0_K2 := EllipticCurve_MontgomeryOriented_KummerProduct(C0,P0);
        iso_E_K2 := iso_E_C0 * iso_C0_K2;
    when "Split mu_4 normal form":
        /*
        c := Explode(ModelInvs);
        s := c^4;
        r := 1/s^2;
        if Y0 ne 0 then
            t0, t1 := Explode([c*Y0,Y1+Y3]);
        else
            t0, t1 := Explode([X1-X3,c*Y2]);
        end if;
        BB_1 := [[c*X0,X1+X3],[X1-X3,c*X2]];
        BB_2 := [[X0*Y0+X2*Y2,X1*Y1+X3*Y3],[X3*Y1-X1*Y3,X0*Y2-X2*Y0]];
        // ...or Twisted form:
        // BB_2 := [[X1*Y3-X3*Y1,X2*Y0-X0*Y2],[X0*Y0+D*X2*Y2,X1*Y1+X3*Y3+2*a*(X1-X3)*(Y1-Y3)]];
        BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
        K2 := EllipticCurve_MontgomeryOriented_Mu4_KummerProduct(c,[t0,t1]);
        iso_E_K2 := map< E->K2 | BB >;
        */
        C1, iso_E_C1 := EllipticCurve_Mu4_NormalForm(E);
        P1 := iso_E_C1(P);
        C0, iso_C1_C0 := EllipticCurve_Mu4_NormalForm(C1);
        P0 := iso_C1_C0(P1);
        K2, iso_C0_K2 := EllipticCurve_MontgomeryOriented_KummerProduct(C0,P0);
        iso_E_K2 := iso_E_C1 * iso_C1_C0 * iso_C0_K2;
    when "Twisted split mu_4 normal form":
        if Characteristic(K) eq 2 then
            c := Explode(ModelInvs);
            if Y0 ne 0 then
                t0, t1 := Explode([c*Y0,Y1+Y3]);
            else
                t0, t1 := Explode([Y1+Y3,c*Y2]);
            end if;
            BB_1 := [[c*X0,X1+X3],[X1-X3,c*X2]];
            BB_2 := [[X0*Y0+X2*Y2,X1*Y1+X3*Y3],[X3*Y1+X1*Y3,X0*Y2+X2*Y0]];
            BB := [ S1 cat S2 : S1 in BB_1, S2 in BB_2 ];
            P1xP1<U0,U1,V0,V1> := ProductProjectiveSpace(K,[1,1]);
            K2 := EllipticCurve_MontgomeryOriented_Mu4_KummerProduct(P1xP1,c,[t0,t1]);
            BB_inv := [[
                (Y1 + Y3)*U0^2*V0,
                (Y0*U0^2 + Y2*U1^2)*V1 + c*Y3*U0*U1*V0,
                (Y1 + Y3)*U1^2*V0,
                (Y0*U0^2 + Y2*U1^2)*V1 + c*Y1*U0*U1*V0],
                [
                (Y1 + Y3)*U0^2*V1,
                (Y2*U0^2 + Y0*U1^2)*V0 + c*Y1*U0*U1*V1,
                (Y1 + Y3)*U1^2*V1,
                (Y2*U0^2 + Y0*U1^2)*V0 + c*Y3*U0*U1*V1]];
            iso_E_K2 := map< E->K2 | BB, BB_inv >;
        else
            require false:
                "Not implemented : Base ring of argument must be of characteristic 2.";
        end if;
    else
        require false:
            "Argument 1 must be an elliptic curve in prescribed normal form.";
    end case;
    return K2, iso_E_K2;
end intrinsic;

