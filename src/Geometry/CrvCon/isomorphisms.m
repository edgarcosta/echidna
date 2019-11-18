//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        ISOMORPHISMS OF CONICS                            //
//                    David Kohel, created June 2002                        //
//         Copyright (C) 2002 David Kohel <kohel@maths.usyd.edu.au>         //
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
// Example:
QQ := Rationals();
P2<x,y,z> := ProjectiveSpace(QQ,2);
R := CoordinateRing(P2); 
C1 := Conic(P2,x^2+y^2-3*z^2);
C2 := Conic(P2,x^2+3*y^2-2*z^2);
Isomorphism(C1,C2);
*/

intrinsic Isomorphism(C1::CrvCon,C2::CrvCon) -> BoolElt, MapIsoSch
    {If C1 and C2 are isomorphic, return an isomorphism from C1 to C2.}
    require Type(BaseField(C1)) eq FldRat and
            Type(BaseField(C2)) eq FldRat :
        "Arguments must be defined over the rationals.";
    bool, phi := IsIsomorphic(C1,C2);
    require bool : "Arguments must be isomorphic.";
    return phi;
end intrinsic;

intrinsic IsIsomorphic(C1::CrvCon,C2::CrvCon) -> BoolElt, MapIsoSch
    {True if and only if C1 is isomorphic to C2, and if so,
    an isomorphism from C1 to C2.}
    
    Q1 := BaseField(C1); Q2 := BaseField(C2);
    require Type(Q1) eq FldRat and Type(Q2) eq FldRat :
        "Arguments must be defined over the rationals.";
    P2 := Ambient(C1); x := P2.1; y := P2.2; z := P2.3;
    D1, m1 := LegendreModel(C1);
    D2, m2 := LegendreModel(C2);
    f1 := DefiningPolynomial(D1);
    f2 := DefiningPolynomial(D2);
    ZZ := Integers();
    cffs1 := [MonomialCoefficient(f1,P2.i^2) : i in [1..3]];
    a1, b1, c1 := Explode([ ZZ!(m1*a) : a in cffs1 ])
	where m1 := LCM([ Denominator(a) : a in cffs1 ]);
    cffs2 := [MonomialCoefficient(f2,P2.i^2) : i in [1..3]];
    a2, b2, c2 := Explode([ ZZ!(m2*a) : a in cffs2 ])
	where m2 := LCM([ Denominator(a) : a in cffs2 ]);
    if HasPoint(C1) then
 	p1 := RationalPoint(C1); 
	bool, p2 := HasPoint(C2);
	if not bool then return false, _; end if;
	P1 := ProjectiveSpace(Rationals(),1);
	gens := [ P1.i*P1.j : i, j in [1..2] | i le j ];
	fncs := DefiningEquations(Parametrization(P1,C1,p1));
	M1 := Matrix(3,[ MonomialCoefficient(f,m) : m in gens, f in fncs ]);
	fncs := DefiningEquations(Parametrization(P1,C2,p2));
	M2 := Matrix(3,[ MonomialCoefficient(f,m) : m in gens, f in fncs ]);
	M := M1*Adjoint(M2); N := M2*Adjoint(M1);
	return true, map< C1 -> C2 |
	    [ &+[ N[i,j]*P2.i : i in [1..3] ] : j in [1..3] ], 
	    [ &+[ M[i,j]*P2.i : i in [1..3] ] : j in [1..3] ] >; 
    end if;
    aa1 := a1*b1; bb1 := a1*c1; cc1 := b1*c1;
    aa2 := a2*b2; bb2 := a2*c2; cc2 := b2*c2;
    n := CommonRepresentation([Integers()|aa1,bb1],[Integers()|aa2,-cc1]);
    CC1 := Conic(P2,aa1*x^2 + bb1*y^2 - n*z^2);
    bool, p1 := HasPoint(CC1);
    if not bool then return false, _; end if;
    CC2 := Conic(P2,aa2*x^2 - cc1*y^2 - n*z^2);
    bool, p2 := HasPoint(CC2);
    if not bool then return false, _; end if;
    if p2[3] ne 0 then 
	v1 := Vector([
	    p1[1]/p1[3]/p2[1], p1[2]/p1[3]/p2[1], p2[2]/p2[3]/p2[1] ]);
    else
	v1 := Vector([ 0, 0, p2[2]/p2[1] ]);
    end if;
    M := EchelonForm(Matrix(
       [[bb1*v1[2],-aa1*v1[1],0 ], [0,cc1*v1[3],-bb1*v1[2] ], [cc1*v1[3],0,-aa1*v1[1]]]));
    u0 := M[1]; v0 := M[2];
    bb0 := aa1*u0[1]^2 + bb1*u0[2]^2 + cc1*u0[3]^2;
    tt0 := aa1*u0[1]*v0[1] + bb1*u0[2]*v0[2] + cc1*u0[3]*v0[3];
    v0 +:= -(tt0/bb0)*u0;
    cc0 := aa1*v0[1]^2 + bb1*v0[2]^2 + cc1*v0[3]^2;
    CC3 := Conic(P2,bb0*x^2 + cc0*y^2 - bb2*z^2);
    bool, p3 := HasPoint(CC3);
    if not bool then return false, _; end if;
    v2 := p3[1]/p3[3]*u0 + p3[2]/p3[3]*v0;
    w0 := cc0*p3[2]/p3[3]*u0 - bb0*p3[1]/p3[3]*v0;
    bool, r0 := IsSquare(cc2/(aa1*w0[1]^2 + bb1*w0[2]^2 + cc1*w0[3]^2));
    v3 := r0*w0;
    M1 := Matrix(3,[ 0,0,aa1, 0,bb1,0, cc1,0,0 ]);
    M2 := Matrix(3,[ 0,0,aa2, 0,bb2,0, cc2,0,0 ]);
    M0 := Adjoint(M2) * Matrix([v1,v2,v3]) * M1;
    N0 := Adjoint(M0);
    eqns1 := [ &+[ N0[i,j]*P2.i : i in [1..3] ] : j in [1..3] ];
    eqns2 := [ &+[ M0[i,j]*P2.i : i in [1..3] ] : j in [1..3] ];
    return true, m1 * iso< D1 -> D2 | eqns1, eqns2 > * Inverse(m2) ;
end intrinsic;
