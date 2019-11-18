//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2010 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic JacobianMatrix(X::Sch,P::Pt) -> AlgMatElt
    {}
    require IsProjective(X) : "Argument 1 must be a projective scheme.";
    A := JacobianMatrix(X);
    S := Eltseq(P);
    return Matrix(Nrows(A),Ncols(A),[ Evaluate(f,S) : f in Eltseq(A) ]);
end intrinsic;

intrinsic TangentLine(C::Crv,P::Pt) -> Crv
    {}
    require IsProjective(C) : "Argument 1 must be a projective curve.";
    require IsNonsingular(P) : "Argument 2 must be a nonsingular point.";
    require Scheme(P) eq C : "Argument 2 must be a point of argument 1.";
    PP := AmbientSpace(C);
    A := JacobianMatrix(C,P);
    R := CoordinateRing(AmbientSpace(C));
    assert Ngens(R) eq Ncols(A);
    return Scheme(PP,[ &+[ R.j*A[i,j] : j in [1..Ngens(R)] ] : i in [1..Nrows(A)] ]);
end intrinsic;

intrinsic TangentLine(P::Pt) -> Crv
    {}
    C := Scheme(P);
    require ISA(Type(C),Crv) and IsProjective(C) : "Arument 1 must be a point on a curve.";
    require IsProjective(C) : "Argument 1 must be a point on a projective curve.";
    require IsNonsingular(P) : "Argument 1 must be a nonsingular point.";
    PP := AmbientSpace(C);
    A := JacobianMatrix(C,P);
    R := CoordinateRing(AmbientSpace(C));
    assert Ngens(R) eq Ncols(A);
    return Scheme(PP,[ &+[ R.j*A[i,j] : j in [1..Ngens(R)] ] : i in [1..Nrows(A)] ]);
end intrinsic;

intrinsic FormalPoint(C::Crv,P::Pt,prec::RngIntElt) -> SeqEnum
    {A power series expansion around the point P.}
    // Note that FormalPoint(P) exists, and works also only
    // for projective curves, however, it was never designed
    // to work for space curves, which were developed later.
    require IsProjective(C) : "Argument 1 must be a point on a projective curve.";
    require IsNonsingular(P) : "Argument 1 must be a nonsingular point.";
    /*
    if Dimension(AmbientSpace(C)) eq 2 then
	return FormalPoint(P);
    end if;
    */
    require assigned C`WeierstrassMorphism :
	"Argument 1 musts be a projective plane curve or have an elliptic model.";
    m := C`WeierstrassMorphism;
    E := Codomain(m);
    xt, yt := FormalGroupExpansion(E,prec);
    LS := Parent(xt); t := LS.1;
    Ot := E(LS)![ xt, yt, 1 ];
    FF := Ring(Parent(P));
    PS := PowerSeriesRing(FF);
    AssertAttribute(PS,"Precision",prec+1);
    Qt := Ot + m(P);
    St := Eltseq(Qt);
    n := -Min([ Valuation(c) : c in St ]);
    // Normalize:
    Tt := Eltseq((E(PS)![ PS | t^n*c : c in St ])@@m);
    n := -Min([ Valuation(c) : c in Tt ]);
    // Normalize:
    return C(PS)![ PS | t^n*c : c in Tt ];
end intrinsic;

