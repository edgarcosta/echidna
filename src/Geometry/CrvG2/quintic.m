//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2008 David Kohel <kohel@iml.univ-mrs.fr>           //
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
Q<q5,q4,q3,q2> := PolynomialRing(QQ,4);
F<q5,q4,q3,q2> := FieldOfFractions(Q);
P<x> := PolynomialRing(F);
f := x^5 + q2*x^3 + q3*x^2 + q4*x + q5;
C := HyperellipticCurve(f);
JJ := IgusaInvariants(C);
j1 := JJ[1]^4*JJ[1]/JJ[5];
j2 := JJ[1]^3*JJ[2]/JJ[5];
j3 := JJ[1]^2*JJ[3]/JJ[5];
j4 := JJ[1]^1*JJ[4]/JJ[5];

h := 1;
DAB_invs := QuarticCMFieldInvariantsWithClassNumber(DBCM,1,2);
for DAB in DAB_invs do
    print "DAB:", DAB; 
    IgLIX := IgusaLIXInvariants(DBIX, DAB)[1];
    //IgSch := IgusaLIXToIgusaScheme(IgLIX);
    jj := IgusaLIXToIgusaInvariantsOverSplittingField(IgLIX);
    j1 := jj[1]^4*jj[1]/jj[5];
    j2 := jj[1]^3*jj[2]/jj[5];
    j4 := jj[1]^1*jj[4]/jj[5];
    [ MinimalPolynomial(J) : J in [j1,j2,j4] ];
end for;

*/

intrinsic QuinticNormalization(f::RngUPolElt) -> RngUPolElt
    {}
    require Degree(f) eq 5 : "Argument must be a polynomial of degree 5.";
    f *:= 1/LeadingCoefficient(f);
    x := Parent(f).1;
    f := Evaluate(f,x-Coefficient(f,4)/5);
    a0, a1, a2, a3 := Explode(Coefficients(f));
    if a3 ne 0 and a2 ne 0 then
	a := a2/a3;
        f := Evaluate(f,a*x)/a^5;
    end if;
    return f;
end intrinsic;

intrinsic RosenhainToPointedQuinticInvariants(xx::SeqEnum[FldElt]) -> SeqEnum
    {}
    if #xx eq 3 then
	t0, t1, t2, t3 := Explode([1] cat xx);
    elif #xx eq 4 then
	t0, t1, t2, t3 := Explode(xx);
    else
	require false: "Argument must have length 3 or 4.";
    end if;
    a := -(t0 + t1 + t2 + t3);
    b := t0*t1 + t0*t2 + t0*t3 + t1*t2 + t1*t3 + t2*t3;
    c := -(t0*t1*t2 + t0*t1*t3 + t0*t2*t3 + t1*t2*t3);
    d := t0*t1*t2*t3;
    return [a,b,c,d];
end intrinsic;

intrinsic PointedQuinticToQuinticInvariants(yy::SeqEnum[FldElt]) -> SeqEnum
    {}
    require #yy eq 4 : "Argument 1 must be a sequence of 4 elements.";
    require Characteristic(Universe(yy)) ne 5 :
	"Universe of argument 1 must not be characteristic 5.";
    a, b, c, d := Explode(yy);
    A := (-2*a^2 + 5*b)/5;
    B := (4*a^3 - 15*a*b + 25*c)/25;
    C := (-3*a^4 + 15*a^2*b - 50*a*c + 125*d)/125;
    D := (4*a^5 - 25*a^3*b + 125*a^2*c - 625*a*d)/3125;
    return [A,B,C,D];
end intrinsic;

intrinsic RosenhainToQuinticInvariants(xx::SeqEnum[FldElt]) -> SeqEnum
    {}
    require #xx in {3,4}: "Argument must have length 3 or 4.";
    require Characteristic(Universe(xx)) ne 5 :
	"Universe of argument 1 must not be characteristic 5.";
    return PointedQuinticToQuinticInvariants(RosenhainToPointedQuinticInvariants(xx));
end intrinsic;

