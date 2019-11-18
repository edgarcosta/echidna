//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//          Construction of a Genus 2 Curve from Igusa Invariants           //
//         Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu.au>         //
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
procedure VerifyHyperellipticCurveFromIgusaInvariants(FF,n)
    assert Type(FF) eq FldFin;
    for i in [1..n] do
	if Characteristic(FF) ne 2 then
	    repeat
		J2, J4, J6, J10 := Explode([ Random(FF) : i in [1..4] ]);
	    until J10 ne 0;
	    J8 := (J2*J6-J4^2)/4;
	    JJ := IgusaToNormalizedIgusaInvariants([ J2, J4, J6, (J2*J6-J4^2)/4, J10 ]);
	else
	    repeat
		J2, J6, J8, J10 := Explode([ Random(FF) : i in [1..4] ]);
	    until J10 ne 0;
	    J4 := Sqrt(J2*J6);
	    JJ := IgusaToNormalizedIgusaInvariants([ J2, J4, J6, J8, J10 ]);
	end if;
	C := HyperellipticCurveFromIgusaInvariants(JJ);
	KK := IgusaToNormalizedIgusaInvariants( IgusaInvariants(C) );
	printf "%o: %o\n", JJ, JJ eq KK; assert JJ eq KK;
    end for;
end procedure;

for p in [2,3,5,7] do
    for r in [1..3] do
        FF<t> := FiniteField(p,r);
        VerifyHyperellipticCurveFromIgusaInvariants(FF,32);
    end for;
end for;
*/

intrinsic HyperellipticCurveFromIgusaClebschInvariants(II::SeqEnum[FldElt]) -> CrvHyp
    {A hyperelliptic curve with given Igusa-Clebsch invariants}
    return HyperellipticCurveFromIgusaClebsch(II); // internal to Magma
end intrinsic;

function MestreConicAndCubicFromIgusaChar3(JJ)
    P<X,Y,Z> := PolynomialRing(Universe(JJ),3);
    J2, J4, J6, J8, J10 := Explode(JJ);
    assert J8 eq J2*J6 - J4^2; //4*J8 eq J2*J6 - J4^2;
    C2 := J2*J4*X^2 + J4^2*X*Y
        + (J2^3*J4 - J2^2*J6 - J2*J4^2 + J10)*X*Z
        + (2*J2^3*J4 + J2^2*J6 + J2*J4^2 - J10)*Y^2
        + (J2^4*J4 + J2^2*J4^2 + J2*J4*J6 - J4^3)*Y*Z
        + (2*J2^3*J4^2 - J2^2*J4*J6 + J4^2*J6 + J4*J10)*Z^2;
    C3 := (J2^5 - J2^3*J4 - J2*J4^2 + J10)*X^3
        + (2*J2^4*J4 + J2^3*J6 + J2^2*J4^2 - J2*J10 - J4^3)*X^2*Y
        + (2*J2^5*J4 + J2^3*J4^2 - J2*J4^3 - J4*J10)*(X^2*Z + X*Y^2)
        + (2*J2^4*J4^2 + J2^3*J4*J6 + J2^2*J4^3 - J2*J4*J10 - J4^4)*X*Y*Z
        + (J2^7*J4 - J2^6*J6 + J2^5*J4^2 + J2^4*J10 - J2^3*J4^3 - J2^3*J6^2
        - J2^2*J4^2*J6 + J2^2*J4*J10 - J2*J4^4 + J2*J6*J10 + J4^3*J6 + J4^2*J10)*X*Z^2
        + (2*J2^8 - J2^5*J6 - J2^4*J4^2 + J2^3*J4*J6
        - J2^3*J10 + J2^2*J4^3 + J2*J4^2*J6 - J2*J4*J10 + J4^4 - J6*J10)*Y^3
        + (J2^7*J4 - J2^6*J6 + J2^4*J10 - J2^3*J6^2 - J2^2*J4^2*J6
        + J2^2*J4*J10 + J2*J4^4 + J2*J6*J10 + J4^3*J6)*Y^2*Z
        + (J2^8*J4 - J2^6*J4^2 - J2^4*J6^2 - J2^3*J4*J10 + J2^2*J4^4
        - J2^2*J6*J10 - J2*J4^3*J6 - J4^5 + J4*J6*J10 - J10^2)*Y*Z^2 
        + (J2^11 + J2^9*J4 - J2^8*J6 - J2^7*J4^2 - J2^6*J4*J6 + J2^6*J10 
        + J2^5*J6^2 - J2^4*J4^2*J6 - J2^3*J4^4 + J2^3*J4*J6^2
        - J2^3*J6*J10 + J2^2*J4^3*J6 - J2^2*J4^2*J10 - J2*J4^2*J6^2
        - J4^4*J6 - J4^3*J10 + J6^2*J10)*Z^3;
    return C2, C3;
end function;


function CardonaQuerCurve5(JJ)
    // Let C: y^2 = x^6 + u1*x^4 + u2*x^2 + 1 be a curve with
    // automorphism ring containing V_4.  The the Igusa invariants
    // are expressions in:
    //    u = u1*u2 and v = u1^3+v1^3.
    // In particular, [J2,J4,J6,J8,J10] equals
    // [
    //    1,
    //    3*(u^2 + 2*u + v)/u^2,
    //    3*(u^2 + u + v)/u^3,
    //    4*(u^4 + 2*u^3 + 2*u^2*v + 2*u^2 + 2*u*v + v^2)/u^4,
    //    2*(u^4 + u^3 + 2*u^2*v + u*v + 3*u + v^2 + v + 4)/u^5
    // ]
    /*
    F<u,v> := FunctionField(FiniteField(5),2);
    JJ := [
        1,
        3*(u^2 + 2*u + v)/u^2,
        3*(u^2 + u + v)/u^3,
        4*(u^4 + 2*u^3 + 2*u^2*v + 2*u^2 + 2*u*v + v^2)/u^4,
        2*(u^4 + u^3 + 2*u^2*v + u*v + 3*u + v^2 + v + 4)/u^5
	];
    */
    J2, J4, J6, _, J10 := Explode(JJ);
    x := PolynomialRing(Universe(JJ)).1;
    if J2 eq 0 then
        if J4 eq 0 then
            f := x^5 + x + 1; // or x^6 + 1;
        else
            w := J6^2/J4^3; 
            f := x^6 + w*x^2 + w^2;
        end if;
	return HyperellipticCurve(f);
    else
	s1 := J4/J2^2; s2 := J6/J2^3; s5 := J10/J2^5;
    end if;
    if s1^2-s1-1 eq 2*s2 and s1^5+2*s1^4-s1^3+s1-1 eq 2*s5 then
	// Automorphism group D8 (u^3 + v^2 = 0):
	return HyperellipticCurve(x^5 + x^3 + (s1+1)*x);
    elif s2 eq 3*s1^2 and (s1+1)^2*s1^3 eq 2*s5 then
	// Automorphism group D12 (u^2 + v):
	return HyperellipticCurve(x^6 + x^3 - (s1+1));
    end if;
    /*
    The hyperelliptic curve C: y^2 = x^6 + u1*x^4 + u2*x^2 + 1, and 
    invariants u, v as above, will have u_den and v_den (as defined
    below) equal to zero if and only if v = -u^2 or v^2 = -u^3.

    In terms of u1 and u2 these are:

              u^2 + v = 0 iff u1^3 + u1^2*u2^2 + u2^3 = 0 (D12 above),
    and
         u^3 + v^2 = 0 iff u1 = u2 or u1^2 + u1*u2 + u2^2 = 0 (D8 above).
    */ 
    u_num := s1^3*s2 - s1^2*s2 - s1*s2^2 - 2*s1*s2 - s2^2 + 2*s5;
    u_den := s1^2*s2^2 + 3*s1^2*s2 - s1*s2^2 - s1*s5 + 2*s2^3 + s2^2;
    /*
    J2*(J4^3*J6 - J2^2*J4^2*J6 - J2*J4*J6^2 - 2*J2^4*J4*J6 - J2^3*J6^2 + 2*J2^4*J10);
    2*J2*J6^3 + J2^4*J6^2 + J4^2*J6^2 + 3*J2^3*J4^2*J6 - J2^2*J4*J6^2 - J2^3*J4*J10;
    */
    v_num := s1^2*(2*s1*(s1+1) + (s2+1))*s2 + s1*s2*(s2+2) + s2^2*(s2-1) + (s1+3)*s5;
    v_den := s1^3*s2 + 3*s1^2*s5 + s1*s2^3 + s1*s2^2 + 2*s2^3 + s2*s5;
    /*
    2*J4^4*J6 + 2*J2^2*J4^3*J6 + J2*J4^2*J6^2 + J2^4*J4^2*J6
        + J2^3*J4*J6^2 + 2*J2^6*J4*J6 + J2^4*J4*J10 + J2^2*J6^3 - J2^5*J6^2 + 3*J2^6*J10;
    J2^2*J4^3*J6 + 3*J2^2*J4^2*J10 + J4*J6^3 + J2^3*J4*J6^2 + 2*J2^2*J6^3 + J2^3*J6*J10;
    */
    u := u_num/u_den; v := v_num/v_den; t := v^2+u^3;
    a0 := u^2*(v+2*u)+t; a1 := 2*(u^2+3*v)*t; a2 := -u^2*v*t; a3 := u^2*t^2;
    f := a0*(x^6 + t^3) + a1*(x^5 + t^2*x) + a2*(x^4 + t*x^2) + a3*x^3;
    return HyperellipticCurve(f);
end function;
    

function CardonaQuerEquationV4(JJ)
    J2,J4,J6,J8,J10 := Explode(JJ);
    if J2 eq 0 then
        return 64*J4^6*J6 + 512*J4^5*J10 + 432*J4^3*J6^3 + 43200*J4^2*J6^2*J10
            + 720000*J4*J6*J10^2 + 729*J6^5 + 3200000*J10^3;
    end if;
    return J2^6*J6^3 - 2*J2^5*J4^2*J6^2 - 72*J2^5*J4*J6*J10 - 432*J2^5*J10^2
        + J2^4*J4^4*J6 + 8*J2^4*J4^3*J10 - 72*J2^4*J4*J6^3 - 48*J2^4*J6^2*J10
        + 136*J2^3*J4^3*J6^2 + 4816*J2^3*J4^2*J6*J10 + 28800*J2^3*J4*J10^2
        + 216*J2^3*J6^4 - 64*J2^2*J4^5*J6 - 512*J2^2*J4^4*J10
        + 1080*J2^2*J4^2*J6^3 - 12960*J2^2*J4*J6^2*J10 - 96000*J2^2*J6*J10^2
        - 2304*J2*J4^4*J6^2 - 84480*J2*J4^3*J6*J10 - 512000*J2*J4^2*J10^2
        - 7776*J2*J4*J6^4 - 129600*J2*J6^3*J10 + 1024*J4^6*J6 + 8192*J4^5*J10
        + 6912*J4^3*J6^3 + 691200*J4^2*J6^2*J10 + 11520000*J4*J6*J10^2
        + 11664*J6^5 + 51200000*J10^3;
end function;


function MestreConicAndCubicFromIgusaChar5(JJ) 
    P<X,Y,Z> := PolynomialRing(Universe(JJ),3);
    J2, J4, J6, J8, J10 := Explode(JJ);
    assert J8 eq J4^2 - J2*J6;  // 4*J8 eq J2*J6 - J4^2;
    if J2 eq 0 then
        // assert J4 ne 0; assert J6 ne 0;
        D30 := J4^6*J6 + 3*J4^5*J10 + 3*J4^3*J6^3 + J6^5; assert D30 ne 0;
        C2 := X*Z + 2*J4*D30*Y^2;
        C3 := J4^2*J6^2*X^3 + (3*J4^6*J6^2 + 4*J4^5*J6*J10 + 4*J4^3*J6^4 + 3*J6^6)*X^2*Y
            + (3*J4^3*J6 + J6^3)*X^2*Z + (2*J4^10*J6^2 + J4^9*J6*J10 + 3*J4^7*J6^4
            + J4^6*J6^3*J10 + 3*J4^4*J6^6 + 2*J4*J6^8)*X*Y^2
            + (3*J4^7*J6 + 3*J4^4*J6^3 + J4*J6^5)*X*Y*Z
            + (3*J4^4 + 4*J4*J6^2)*X*Z^2
            + (J4^14*J6^2 + 3*J4^13*J6*J10 + 4*J4^11*J6^4 + 3*J4^10*J6^3*J10
            + J4^8*J6^6 + J4^7*J6^5*J10 + 2*J4^5*J6^8 + 2*J4^2*J6^10)*Y^3
            + (J4^11*J6 + 3*J4^10*J10 + J4^8*J6^3 + 4*J4^7*J6^2*J10 + 3*J4^2*J6^7)*Y^2*Z
            + 4*J4^2*J6*Z^3;
	has_point := true; P := [0, 0, 1];
    else
        C2 := J2*X^2 + 3*J4*J6*X*Z + (3*J2^6*J6 + J2^5*J4^2 + 3*J2^4*J4*J6
            + J2^3*J4^3 + J2^3*J6^2 - J2^2*J4^2*J6 - J2*J4^4)*Y^2
            + (4*J2^6*J6 + 3*J2^5*J4^2 - J2^4*J10 + 3*J2^3*J4^3 + J2^3*J6^2
            + 2*J2*J4^4 + 3*J2*J4*J6^2 + 2*J4^3*J6)*Y*Z
            + (3*J2^6*J6 + J2^5*J4^2 + 2*J2^4*J4*J6 + J2^4*J10 + J2^3*J4^3
            + 2*J2^3*J6^2 + 3*J2^2*J4^2*J6 + J2^2*J4*J10 - J2*J4^4
            + 3*J2*J4*J6^2 + 3*J4^3*J6 + 3*J6^3)*Z^2;
        C3 := (J2^3 + 3*J2*J4)*X^3 + (J2^5*J4 - J2^3*J4^2
            - J2^2*J4*J6 + 3*J2*J4^3)*X^2*Y
            + (4*J2^4*J6 + 3*J2^3*J4^2 + 2*J2*J4^3 + 2*J2*J6^2 + 3*J4^2*J6)*X^2*Z
            + (J2^6*J4*J6 - J2^6*J10 + 3*J2^5*J6^2
            + 3*J2^4*J4^2*J6 + 3*J2^3*J4*J6^2 + 2*J2^2*J4^3*J6)*X*Y^2
            + (3*J2^6*J4*J6 + 2*J2^6*J10 - J2^4*J4*J10 + 3*J2^3*J4*J6^2
            + 3*J2^2*J4^3*J6 + 2*J2^2*J6^3 + 3*J2*J4^2*J6^2 - J4^4*J6)*X*Y*Z
            + (J2^6*J4*J6 - J2^6*J10 + 2*J2^5*J6^2
            + J2^4*J4*J10 + 3*J2^3*J4*J6^2
            + 2*J2^3*J6*J10 + 3*J2^2*J4^3*J6 + J2^2*J4^2*J10 + 2*J2^2*J6^3
            + J2*J4^2*J6^2 + J4^4*J6 + 3*J4*J6^3)*X*Z^2
            + (-J2^10*J10 + 3*J2^9*J4^3 + 3*J2^9*J6^2 + J2^8*J4^2*J6 - J2^8*J4*J10
            - J2^7*J4^4 + 3*J2^7*J6*J10 + J2^6*J4^2*J10 + J2^6*J6^3 - J2^5*J4^5
            + J2^5*J4^2*J6^2 - J2^4*J4^4*J6 - J2^4*J4*J6^3 - J2^3*J4^3*J6^2
            - J2^2*J4^5*J6 - J2*J4^7)*Y^3 +
            (3*J2^10*J4*J6 + 3*J2^10*J10 + 2*J2^9*J4^3 + 2*J2^9*J6^2 + J2^8*J4^2*J6
            + J2^7*J4^4 + J2^7*J4*J6^2 + J2^7*J6*J10 + 2*J2^6*J4^3*J6 + J2^6*J4^2*J10
            + 3*J2^6*J6^3 - J2^5*J4^5 + J2^5*J4^2*J6^2 + 3*J2^5*J4*J6*J10 + 3*J2^4*J4^4*J6
            - J2^4*J4^3*J10 + 3*J2^4*J4*J6^3 + 3*J2^3*J4^6 + 3*J2^3*J6^4 + 2*J2^2*J4^5*J6
            + 2*J2^2*J4^2*J6^3 + 3*J2*J4^7 + 3*J4^6*J6)*Y^2*Z
            + (4*J2^10*J4*J6 + 2*J2^10*J10 + 2*J2^9*J4^3 + 2*J2^9*J6^2
            + J2^8*J4^2*J6 + 2*J2^8*J4*J10 + J2^7*J4^4 - J2^7*J4*J6^2
            + J2^7*J6*J10 + J2^6*J4^3*J6 + 3*J2^6*J4^2*J10 + J2^5*J4^2*J6^2
            + 3*J2^5*J4*J6*J10 + J2^4*J4^4*J6 + J2^4*J4*J6^3 - J2^3*J4^6 + 2*J2^3*J4^3*J6^2
            - J2^3*J6^4 + J2^2*J4^5*J6 - J2^2*J4^4*J10 + 2*J2*J4^7 + J2*J4^4*J6^2
            - J2*J4*J6^4 - J4^6*J6 + 2*J4^3*J6^3)*Y*Z^2
            + (3*J2^10*J4*J6 + J2^10*J10 + 3*J2^9*J4^3 + 3*J2^9*J6^2
            + 2*J2^8*J4^2*J6 - J2^8*J4*J10 - J2^7*J4^4 - J2^7*J4*J6^2
            - J2^6*J4^3*J6 + J2^6*J4^2*J10 + 3*J2^6*J6^3 + 2*J2^5*J4^5
            + 3*J2^5*J4*J6*J10 + J2^5*J10^2 + J2^4*J4^4*J6
            + 3*J2^4*J4^3*J10 - J2^4*J4*J6^3 - J2^4*J6^2*J10 + 3*J2^3*J4^6
            + 2*J2^3*J4^3*J6^2 + 3*J2^3*J4^2*J6*J10 + J2^3*J6^4 + 3*J2^2*J4^5*J6
            + J2^2*J4^4*J10 + J2^2*J4^2*J6^3 + 3*J2^2*J4*J6^2*J10 + J2*J4^7
            - J2*J4^4*J6^2 + 3*J4^6*J6 + 3*J4^3*J6^3)*Z^3;
	has_point := false; P := [0, 0, 0];
    end if;
    return C2, C3, has_point, P;
end function;

function GeomAutType(JJ)
    // This just distinguishes C2 and V4.
    FF := Universe(JJ);
    J2, J4, J6, J8, J10 := Explode(JJ); 
    if Characteristic(FF) eq 2 then
        error if true, "Not implemented error";
    elif Characteristic(FF) eq 3 then
        V4_Test := J2^6*J6^3 + J2^5*J4^2*J6^2 + J2^4*J4^3*(J4*J6 - J10)
            + J2^3*J4^2*J6*(J4*J6 + J10) - J2^2*J4^4*(J4*J6 - J10)
            + J2*J4^2*J10^2 + J4^6*J6 - J4^5*J10 - J10^3;
        if V4_Test eq 0 then
            return "V4";
        else
            return "C2";
        end if;
    else
        V4_Test := J2^6*J6^3 - 2*J2^5*(J4^2*J6^2 + 36*J4*J6*J10 + 216*J10^2)
            + J2^4*(J4^4*J6 + 8*J4^3*J10 - 72*J4*J6^3 - 48*J6^2*J10)
            + 8*J2^3*(17*J4^3*J6^2 + 602*J4^2*J6*J10 + 3600*J4*J10^2 + 27*J6^4)
            - 8*J2^2*(8*J4^5*J6 + 64*J4^4*J10 - 135*J4^2*J6^3 + 1620*J4*J6^2*J10
            + 12000*J6*J10^2)
            - 32*J2*(72*J4^4*J6^2 + 2640*J4^3*J6*J10 + 16000*J4^2*J10^2
            + 243*J4*J6^4 + 4050*J6^3*J10)
            + 16*(64*J4^6*J6 + 512*J4^5*J10 + 432*J4^3*J6^3 + 43200*J4^2*J6^2*J10
            + 720000*J4*J6*J10^2 + 729*J6^5 + 3200000*J10^3);
        if V4_Test eq 0 then
            return "V4";
        else
            return "C2";
        end if;
    end if;
end function;

function HyperellipticCurveFromAbsoluteIgusaChar2(jj)
    // This follows CNP, but j1, j2, j4 here denote Igusa's invariants.
    // It does not make sense to follow CNP, since the invariants are
    // denoted differently according to the model of the curve.
    FF := Universe(jj);
    x := PolynomialRing(FF).1;
    if jj[1] eq 0 then
        assert &and[ jj[i] eq 0 : i in [1..6] ];
        j7, j8, j9, j10 := Explode(jj[[7..10]]);
        if j7 ne 0 or j8 ne 0 then
	    // The intermediate case.
	    if j7 ne 0 then 
		assert j8*j9 eq j7^3;
		bool, b := IsPower(j7,8); assert bool;
		bool, c := IsPower(j8,8); assert bool;
		g, h := Explode([x^4 + b*x^2 + 1, c*x]);
	    else
		bool, c := IsSquare(1/j8); assert bool;
		g, h := Explode([c*x^4 + 1, x ]);
	    end if;
        else
	    // The supersingular case.
	    assert j9 eq 0;
	    if j10 ne 0 then
		bool, c := IsPower(jj[10],8); assert bool;
		g, h := Explode([x^5 + c*x^3, c^2 ]);
	    else
		g, h := Explode([x^5, 1]);
	    end if;
        end if;
    else
        j1, j2, j4 := Explode(jj[[1,2,4]]);
        u1 := Sqrt(j1)^-1; 
        u2 := Sqrt(j2) * u1;
        u4 := Sqrt(j4) * u1 + u2^3*(u2 + 1);
        num := u2^2 + u4;
        den := u1 + u2*u4;
        if den eq 0 then
            // Automorphism group contains an extra involution.
            if num eq 0 then
                // j1 = 1/u2^6
                // j2 = 1/u2^4
                // j4 = (u2^4 + u2^2 + 1)/u2^2
                h := x^3 + x + 1;
                g := u2*(x^2 + x);
            else
                // j2 = j1*u2^2
                // j4 = (j1^4 + j1*j2^4 + j2^5)/(j1^3*j2)
                h := x^2 + x;
                g := u2*(x^3 + x) + 1/Sqrt(Sqrt(j2));
            end if;
        else
            if num eq 0 then
                s := den;
                h := x^3 + s;
                g := s*(x + u2);
            else
                u0 := den^-1;
                s := u0^2 * num^3;
                a := u0^2 * (u1 + u2^3) * num^2;
                c := u0^4 * num^3 * (u1 * num^2 + u2 * (u1 + u2^3)^2);
                h := x^3 + s*x + s;
                g := a*x^2 + a*x + c;
            end if;
        end if;
    end if;
    return HyperellipticCurve(g*h,h);
end function;

function HyperellipticCurveFromAbsoluteIgusaChar3(jj)
    // Following Cardona and Quer plus Howe (supersingular case).
    FF := Universe(jj);
    x := PolynomialRing(FF).1;
    if jj[1] ne 0 then
        // Ordinary case: J2 != 0
        j1, j2, j3, j4 := Explode(jj[[1..4]]);
        i1 := 1/j1;
        JJ := [ 1, j2*i1, j3*i1, j4*i1, i1 ];
        if GeomAutType(JJ) eq "V4" then
            // Extra involution...
            //   y^2 = x^6 + u1*x^4 + u2*x^2 + 1
            // Following Cardona and Quer.
            num := ((j1 - j2)*j2^2 - j1^2*(j2 - j3 + 1))*i1^3;
            den := (j1*j3 - j1 + j2)*i1^2;
            if den eq 0 then
                // These should be caught in GeomAutType:
                //   u1 = u2, u1 = u2^2, or u1^2 = u2 
                t2 := -JJ[2];
                if t2 eq 0 then
                    // u1 = u2^2 or u2 = u1^2:
                    assert {JJ[3],JJ[4],JJ[5]} eq {JJ[3]};
                    bool, u1 := IsPower(-1/JJ[3],9); assert bool;
                    f := x^6 + u1*x^4 + u1^2*x^2 + 1; 
                elif JJ eq [1,-t2,-(t2+1)*(t2-1)^2,-t2^3+t2-1,-(t2-1)^2] then
                    // u1 = u2 (and t2 = ((u1-1)/u1)^2:
                    // See Cardona and Quer.
                    bool, t1 := IsSquare(t2);
                    if bool then
                        // Equivalently we have:
                        //    f := x^6 + u1*x^4 + u1*x^2 + 1,
                        // where u1 = 1/(1-t1).
                        f := x^5 + t1*x^3 + x;
                    else
                        f := x^5 + x^3 + 1/t2*x;
                    end if;
                end if;
            else
                nr := num/den;
                // assert nr ne 0: 
                // See Cardona and Quer for the case nr = 0.
                // This implies that j1 = 1, hence does occur here.
                bool, tr := IsPower(nr^2*(j1 + j2)*i1 + nr,3); assert bool;
                bool, sr := IsSquare(tr^2-nr);
                if bool then
                    u1 := -(tr + sr); 
                    u2 := u1 - sr;
                    f := x^6 + u1*x^4 + u2*x^2 + 1;
                else
                    u := nr;
                    v := tr^3;
                    w := (tr^2-nr)^3;
                    a0 := v^2 + u^2*v + u^3;
                    a1 := -u^2*w;
                    a2 := -u^2*v*w;
                    a3 := -(u^2+v)*w^2;
                    f := a0*(x^6 + w^3) + a1*(x^5 + w^2*x)
                        + a2*(x^4 + w*x^2) + a3*x^3;
                end if;
            end if;
        else
            C2, C3 := MestreConicAndCubicFromIgusaChar3(JJ);
            repeat
                x2 := Random(FF);
                bool, x1 := HasRoot(Evaluate(C2, [ x,x2,1]));
            until bool;
            P2<U,V> := PolynomialRing(FF,2);
            g := Evaluate(C2,[ x1+U*V, x2+U, 1]);
            A := Coefficient(g,U,2);
            B := Coefficient(g,U,1);
            assert Evaluate(C2,[ A*x1-B*V, A*x2-B, A]) eq 0;
            P := [ Evaluate(F,[1,x]) : F in [ A*x1-B*V, A*x2-B, A] ];
            f := Evaluate(C3,P);
        end if;
    elif jj[5] ne 0 then
        // J2 = 0, J4 != 0
        // jj: [ 0, 0, 0, 0,
        //     J4*J6/J10, -J4^5/J10^2, -J4^2*J6^2/J10^2, J6^5/J10^3, ... ]; 
        // where J8 = -J4^2 (since J2 = 0).
        assert &and[ jj[i] eq 0 : i in [1..4] ];
        uu := jj[5]^3/jj[8]; // assert jj[6]/jj[7] eq -uu;
        JJ := [ 0, uu, uu, -uu^2, uu^2/jj[5] ];
        _, J4, J6, _, J10 := Explode(JJ);
        C2, C3 := MestreConicAndCubicFromIgusaChar3(JJ);
        assert Evaluate(C2,[1,0,0]) eq 0;
        if J4^6*J6 - J4^5*J10 - J10^3 eq 0 then
            // The conic C2 splits into two lines one of which is:
            //   Y + J4^5/(J4^5 + J10^2)*Z,
            // so we must find an explicit parametrization.
            f := x^6 + u2*x^2 + u2 where u2 := jj[6];
        else
            // Use a pre-computed parametrization:
            PF := PolynomialRing(FF); x := PF.1;
            x1 := J4^4*x^2 + J4^5*x - J4*J10*(J4*J6 + J10);
            x2 := J4^2*J10*x - J4^3*(J4*J6 + J10);
            x3 := -J4^4*x - (J4^5 - J10^2);
            assert Evaluate(C2,[x1,x2,x3]) eq 0;
            f := Evaluate(C3,[x1,x2,x3]);
        end if;
    elif jj[6] ne 0 then
	// J6 = 0 and J4 != 0
	// uu := jj[6];
	// JJ := [ 0, uu, 0, -uu^2, uu^2 ];
	// _, J4, _, _, J10 := Explode(JJ);
	/*
	J4 := jj[6]; // J10 := J4^2;
	JJ := [ 0, J4, 0, -J4^2, J4^2 ];
        C2, C3 := MestreConicAndCubicFromIgusaChar3(JJ);
	// Use a pre-computed parametrization:
	PF := PolynomialRing(FF); x := PF.1;
	x1 := J4^2*x^2 + J4^3*x - J4^3;
	x2 := J4^2*x - J4^3;
	x3 := -J4^2*x - J4^3 + J4^2;
	assert Evaluate(C2,[x1,x2,x3]) eq 0;
	f := Evaluate(C3,[x1,x2,x3]);
	*/
	// Caution: Also singular at u = 1!
	u := jj[6];
	if u eq -1 then
	    f := x^6 + 2*x^4 + x^3 + 2*x + 1;
	else
	    f := x^6 + u*(u+1)*x^4 - u^2*x^3 + u^2*(u+1)*(u^2+u-1)*x - u^5*(u-1);
	end if;
    elif jj[8] ne 0 then
        // Supersingular case:
        // J2 = J4 = J8 = 0; J6 != 0
        // N.B. See Everett Howe's article on supersingular 
        //      genus 2 curves in characteristic 3.
        // jj: [ 0, 0, 0, 0, 0, 0, 0, J6^5/J10^3, 0, 0 ];
        assert &and[ jj[i] eq 0 : i in [1..10] | i ne 8 ];
        // True over a finite field of characteristic 3:
        // bool, c := IsPower(1/jj[8],3); // assert bool; 
        // f := x^6 + x^3 + c*x + 1;
        f := x^6 + c^2*x^3 + c^3*x + c^4 where c := jj[8];
    else
        // Special supersingular curve with small CM:
        assert &and[ jj[i] eq 0 : i in [1..10] ];
        f := x^5 + 1;
    end if;
    return HyperellipticCurve(f);
end function;

function HyperellipticCurveFromAbsoluteIgusaChar5(jj)
    // Following Cardona and Quer, plus explicit integral transform of
    // Mestre's conic and cubic (removing copy of conic from cubic).
    FF := Universe(jj);
    x := PolynomialRing(FF).1;
    if jj[1] eq 0 then
	// J2 == 0
        assert &and[ jj[i] eq 0 : i in [1..4] ];
        if jj[5] eq 0 then
            // J4.J6 == 0
            if jj[6] ne 0 then
                // J4 != 0 and J6 == 0
                // JJ = [0,1/u,0,1/u^2,2/u^3]
                u := 1/jj[6]; // = J10^2/J4^5
                f := x^5 + x^4 + 2*u;
            elif jj[8] ne 0 then
                // J4 == 0 and J6 != 0
                f := x^5 + t^2*x^2 + 2*t^3 where t := jj[8];
            else
		// J4 == J6 == 0
                f := x^5 + x; // or x^6 + 1, or x^5 + x + 1.
            end if;
        else
	    // J4 != 0 and J6 != 0
	    // JJ == [ 0, u, u, u^2, u^2/j5 ] where u = j5^3/j8
	    if jj[5]*jj[6] + 3*jj[6] + 3*jj[5]^3 + jj[8] eq 0 then
		// Cardona and Quer's characterization of V4 moduli.
		w := 3*jj[5]^3/jj[9]; // = 3/u = 3*J6^2/J4^3
		// JJ == [ 0, u, u, u^2, 3*(u-1)^2 ]
		if w ne 3 then
		    f := x^6 + w*x^2 + w^2;
		else
		    f := x^5 + x^4 - x^3 + x^2 + x;
		end if;
	    else
		u := jj[5]^3/jj[8];         
		JJ := [0, u, u, u^2, u^2/jj[5] ]; 
		C2, C3, bool, P := MestreConicAndCubicFromIgusaChar5(JJ);
		if bool then
		    x1, x2 := Explode(P); assert P[3] eq 1;
		else
		    // This assumes that FF is a finite field:
		    error if Type(FF) ne FldFin, 
			"Argument must be a sequence of finite field elements to solve conic.";
		    repeat
			x2 := Random(FF);
			bool, x1 := HasRoot(Evaluate(C2, [ x,x2,1]));
		    until bool;
		end if;
		P2<U,V> := PolynomialRing(FF,2);
		g := Evaluate(C2,[ x1+U*V, x2+U, 1]);
		A := Coefficient(g,U,2);
		B := Coefficient(g,U,1);
		assert Evaluate(C2,[ A*x1-B*V, A*x2-B, A]) eq 0;
		P := [ Evaluate(F,[1,x]) : F in [ A*x1-B*V, A*x2-B, A] ];
		f := Evaluate(C3,P);
	    end if;
        end if;
    elif jj[1] ne 0 then
        j1, j2, j3, j4 := Explode(jj[[1..4]]);
        if j2 eq -j1 and j3 eq 3*j1 and j4 eq 3*j1 then
            // f := x^5 + x^3 + 3*(j1^2+j1+1) - j2;
            f := x^5 - j1*x^3 + j1^2;
        else
            i1 := 1/j1; 
	    JJ := [ 1, j2*i1, j3*i1, j4*i1, i1 ];
            if JJ[2]^2 - JJ[2] + 3*JJ[3] eq 1 and 
                (JJ[2]^2 + 2*JJ[2] + 4)*JJ[2]^3 + JJ[2] + 3*JJ[5] eq 1 then
                // Automorphism group D8: 
                f := x^5 + x^3 + (JJ[2] + 1)*x;
            elif JJ[3] eq 3*JJ[2]^2 and JJ[5] eq 3*(JJ[2]+1)^2*JJ[2]^3 then
                // Automorphism group D12:
		f := x^6 + x^3 - (JJ[2] + 1);
            elif CardonaQuerEquationV4(JJ) eq 0 then
                // Automorphism group V4: 
                return CardonaQuerCurve5(JJ);
	    else
		C2, C3, bool, P := MestreConicAndCubicFromIgusaChar5(JJ);
		if bool then
		    x1, x2, x3 := Explode(P); assert x3 eq 1;
		else
		    // This assumes that FF is a finite field:
		    error if Type(FF) ne FldFin, 
			"Argument must be a sequence of finite field elements to solve conic.";
		    x3 := 1;
		    repeat
			x2 := Random(FF);
			bool, x1 := HasRoot(Evaluate(C2,[x,x2,x3]));
		    until bool;
		end if;
		P2<U,V> := PolynomialRing(FF,2);
		g := Evaluate(C2,[ x1+U*V, x2+U, 1]);
		A := Coefficient(g,U,2);
		B := Coefficient(g,U,1);
		assert Evaluate(C2,[ A*x1-B*V, A*x2-B, A]) eq 0;
		P := [ Evaluate(F,[1,x]) : F in [ A*x1-B*V, A*x2-B, A] ];
		f := Evaluate(C3,P);
	    end if;
        end if;
    end if;
    return HyperellipticCurve(f);
end function;

intrinsic HyperellipticCurveFromAbsoluteIgusaInvariants(jj::SeqEnum[FldElt]) -> CrvHyp
    {A hyperelliptic curve from given absolute Igusa invariants, using
    Mestre's algorithm in in characteristic > 3.  For characteristic 2 or 3
    the Igusa invariants must be of an ordinary genus 2 curve.}
    FF := Universe(jj);
    x := PolynomialRing(FF).1;
    if Characteristic(FF) eq 2 then
        return HyperellipticCurveFromAbsoluteIgusaChar2(jj);
    elif Characteristic(FF) eq 3 then
        return HyperellipticCurveFromAbsoluteIgusaChar3(jj);
    elif Characteristic(FF) eq 5 then
        return HyperellipticCurveFromAbsoluteIgusaChar5(jj);
    else // Characteristic(FF) ge 7
        // jj: [ J2^5/J10, J2^3*J4/J10, J2^2*J6/J10, J2*J8/J10, J4*J6/J10, ... ]
	if jj[1] ne 0 then
	    // J2 != 0
            bool, uu := IsInvertible(jj[1]);
            JJ := [ 1, uu*jj[2], uu*jj[3], uu*jj[4], uu ];
        elif jj[5] ne 0 then
	    // J2 == 0, J4 != 0, J6 != 0
            // jj: [ 0, 0, 0, 0,
            //     J4*J6/J10, J4*J8^2/J10^2, J6^2*J8/J10^2, J6^5/J10^3, ... ];
            uu := jj[5]^3/jj[8];
            JJ := [ 0, uu, uu, uu*jj[6]/jj[7], uu^2/jj[5] ];
        elif jj[8] ne 0 then
	    // J2 == 0, J4 == 0, J6 != 0
            // jj: [ 0, 0, 0, 0, 0, 0, 0, J6^5/J10^3, 0, 0 ];
            j6 := jj[8]^2; j10 := j6*jj[8];
            JJ := [ 0, 0, j6, 0, j10 ];
	elif jj[6] ne 0 then
	    // J2 == 0, J6 == 0, J4 != 0, (&& J8 == -J4^2/4)
	    // jj = [ 0, 0, 0, 0, 0, 0, J4^5/(16*J10^2), 0, 0, -J4^10/(1024*J10^4) ]
	    //    = [ 0, 0, 0, 0, 0, 0, s, 0, 0, -J4^10/(1024*J10^4) ]
	    // JJ = [ 0, s, 0, -s^2/4, -s^2/4 ] where s := jj[6];
	    s := jj[6];
	    t := 1 + 5^5/(8*s); // (8*s + 5^6)/(8*s)
	    if t ne 0 then
		f := x^6 - 5*t*x^4 + 15*t^2*x^2 + 16*t^3*x + 5*t^3;
	    else
		// t == 0 when 8*s + 5^5 == 0; the following equation is valid 
		// for any square value of t after taking a square root of t.
		f := x^6 - 5*x^4 + 15*x^2 + 16*t*x + 5;
   	    end if;
	    return HyperellipticCurve(f);
	else
	    // J2 == 0, J4 == 0, J6 == 0, hence J8 = (J2*J6 - J4^2)/4 = 0
	    require jj eq [0,0,0,0,0,0,0,0,0,0] :
		"Argument is not valid sequence of absolute Igusa invariants.";
	    return HyperellipticCurve(x^5 - 1);
        end if;
        II := IgusaToIgusaClebschInvariants(JJ);
        return HyperellipticCurveFromIgusaClebschInvariants(II);
    end if;
end intrinsic;

intrinsic HyperellipticCurveFromIgusaInvariants(JJ::SeqEnum[FldElt]) -> CrvHyp
    {}
    require #JJ eq 5 and JJ[5] ne 0 : 
	"Argument must consist of five Igusa invariants (with JJ[5] nonzero).";
    require JJ[1]*JJ[3]-JJ[2]^2 eq 4*JJ[4] : 
	"Argument JJ = [J2,J4,J6,J8,J10] must satisfy 4*J8 = J2*J6-J4^2.";
    FF := Universe(JJ);
    p := Characteristic(FF);
    if p gt 5 then
        II := IgusaToIgusaClebschInvariants(JJ);
        return HyperellipticCurveFromIgusaClebschInvariants(II);
    end if;
    jj := IgusaToAbsoluteIgusaInvariants(JJ);
    return HyperellipticCurveFromAbsoluteIgusaInvariants(jj);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
