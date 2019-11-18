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
// Example of the use of this Frobenius representation on the 16-torsion
// in order to prove that the endomorphism ring is non-maximal at 2.

ZZ := IntegerRing();
PZ<x> := PolynomialRing(ZZ);
chi := x^4 - 12*x^3 + 490*x^2 - 2916*x + 59049;
K<pi> := NumberField(chi);
OK := MaximalOrder(K);
FF<t> := GF(3,5);
JJ := [ 1, t^143, t^90, t^46, t^117 ];
C := HyperellipticCurveFromIgusaInvariants(JJ);
J := Jacobian(C);
if FrobeniusCharacteristicPolynomial(C) ne chi then
    C := QuadraticTwist(C);
end if;
assert FrobeniusCharacteristicPolynomial(C) eq chi;
Pi := FrobeniusTorsionRepresentation(J,16);
r := pi^3 + 7*pi^2 + 5*pi - 1;
assert r/16 in OK;
R := Pi^3 + 7*Pi^2 + 5*Pi - 1;
assert R ne 0;
*/


intrinsic FrobeniusTorsionRepresentation(J::JacHyp,N::RngIntElt :
    Check := true) -> AlgMatElt, SeqEnum
    {The representation matrix on the N-torsion subgroup for a prime power N,
    followed by the N-torsion basis.}
    bool, p, k := IsPrimePower(N);
    require bool : "Argument 2 must be a prime power.";
    g := Dimension(J);
    FF := BaseRing(J);
    KK := MaximalOrderTorsionSplittingField(J,p,k);
    print KK;
    JK := BaseExtend(J,KK);
    G, m := TorsionSubgroup(JK,N);
    require AbelianInvariants(G) eq [ N : i in [1..2*g] ] :
	"Not implemented for non-maximal endomorphism rings...";
    X := [ m(G.i) : i in [1..Ngens(G)] ];
    Y := [ Frobenius(x,FF) : x in X ];
    u := PrimitiveElement(KK)^((#KK-1) div N);
    R := ResidueClassRing(N);
    T := Matrix([ [ R | Log(u,WeilPairing(x,y,N)) : x in X ] : y in Y ]);
    S := Matrix([ [ R | Log(u,WeilPairing(x,y,N)) : x in X ] : y in X ]);
    A := T * S^-1;
    if Check then
	ZZ := IntegerRing();
	assert [ &+[ ZZ!A[i,j] * X[j] : j in [1..4] ] : i in [1..4] ] eq Y;
    end if;
    return A, X;
end intrinsic;
