//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
EXAMPLES:

prec := 1048;
p := 3; n := 3;
FF<w> := FiniteField(p,n);
PF<x> := PolynomialRing(FF);
B :=
    [
    [ w^18, w^12, w^24 ],
    [ w^22, w^20, 2 ],
    [ w^14, w^8, 2 ]
    ];

tt := CanonicalLiftRosenhainInvariants(B[3],1,prec);
jj := RosenhainToAbsoluteIgusaInvariants(tt)[[1,2,4]];
[ 
    AlgebraicRelations(JJ,I : RingPrecision := prec-48)[1] : 
    I in [[6,0,0],[0,6,0],[0,0,6]]
    ];

*/

function DxPhi(DPhi,zz)
    return Matrix([ [ Evaluate(f,zz) : f in DPhi[i] ] : i in [1..3] ]);
end function;

function DuPhi(DPhi,zz)
    return Matrix([ [ Evaluate(f,zz) : f in DPhi[i] ] : i in [4..6] ]);
end function;

function DxPsi(DPsi,zz)
    return Matrix([ [ Evaluate(f,zz) : f in DPsi[i] ] : i in [1..3] ]);
end function;

function DuPsi(DPsi,zz)
    return Matrix([ [ Evaluate(f,zz) : f in DPsi[i] ] : i in [4..6] ]);
end function;

function DyPsi(DPsi,zz)
    return Matrix([ [ Evaluate(f,zz) : f in DPsi[i] ] : i in [7..9] ]);
end function;

function NewtonAGMLifts(xx,uu,r,Phi,Psi,DPhi,DPsi : ExtraPrecision := 1)
    SS := Universe(xx);
    VS := RSpace(SS,3);
    prec := Precision(SS);
    if prec eq 1 then
	return { xx };
    elif prec le 2*ExtraPrecision+1 then 
	extra := 0;
    else
	extra := ExtraPrecision;
    end if;
    p := ResidueCharacteristic(SS);
    prec1 := (prec+1) div 2;
    vprintf CanonicalLift : "REDUCING TO LOWER PRECISION: %o\n", prec1;
    S1 := ChangePrecision(SS,prec1+extra); AssignNames(~S1,["t"]);
    x1 := ChangeUniverse(xx,S1);
    u1 := ChangeUniverse(uu,S1);
    xx_half_sols_S1 := NewtonAGMLifts(x1,u1,r,Phi,Psi,DPhi,DPsi : ExtraPrecision := ExtraPrecision);
    if extra gt 0 then
	S1 := ChangePrecision(SS,prec1); AssignNames(~S1,["t"]);
	V1 := RSpace(S1,3);
	xx_half_sols_S1 := { V1!xi : xi in xx_half_sols_S1 };
    end if;
    vprintf CanonicalLift : "LIFTED HALFWAY TO PRECISION: %o\n", prec1;
    if GetVerbose("CanonicalLift") ge 2 then
	print "LIFTED PRECISIONS VERIFICATION:", 
	    [ Min([ Valuation(Evaluate(f,zz_half)) : f in Psi ])
	    where zz_half := Eltseq(xx_half) cat Eltseq(uu_half) cat Eltseq(yy_half)
	    where yy_half := [ GaloisImage(xx_half[i],r) : i in [1..3] ]
	    where uu_half := [ HenselLift(Richelot[i],S1!uu[i]) : i in [1..3] ]
	    where Richelot := [
	    Polynomial([t1*t2 - t1 + t2, - 2*t2, 1]),
	    Polynomial([-t0*t2, 2*t2, -1]),
	    Polynomial([-t0*t1, 2*t1, (t0 - t1 - 1) ]) ]
	    where t0,t1,t2 := Explode(Eltseq(xx_half)) : xx_half in xx_half_sols_S1 ];
    end if;
    S2 := ChangePrecision(SS,prec-prec1); AssignNames(~S2,["t"]);
    V2 := RSpace(S2,3);
    MatS2 := MatrixAlgebra(S2,3);
    xx_half_sols_SS:= { VS!ChangeUniverse(Eltseq(xx),SS) : xx in xx_half_sols_S1 };
    xx_sols_SS := {};
    PS := PolynomialRing(SS); x := PS.1;
    for xx_half in xx_half_sols_SS do
	assert &and[ Valuation(xx[i]-xx_half[i]) gt 0 : i in [1..3] ];
	Richelot := [
	    x^2 - 2*t2*x + t1*t2 - t1 + t2,
	    -x^2 + 2*t2*x - t0*t2,
	    (t0 - t1 - 1)*x^2 + 2*t1*x - t0*t1 ]
	    where t0,t1,t2 := Explode(Eltseq(xx_half));
	uu_half := [ HenselLift(Richelot[i],uu[i]) : i in [1..3] ];
	yy_half := VS![ GaloisImage(x,r) : x in Eltseq(xx_half) ];
	zz_half := Eltseq(xx_half) cat Eltseq(uu_half) cat Eltseq(yy_half);
	A := MatS2!DyPsi(DPsi,zz_half);
	B := MatS2!(
	    DxPsi(DPsi,zz_half) - DxPhi(DPhi,zz_half) * DuPhi(DPhi,zz_half)^-1 * DuPsi(DPsi,zz_half));
	C := V2![ Evaluate(f,zz_half) div p^prec1 : f in Psi ];
	xx_sols_new := { };
	for dx_j in ArtinSchreierRoots(A,B,C,r) do
	    //print "  dx_j =", dx_j;
	    xx_full := xx_half + p^prec1*(VS!dx_j);
	    Richelot := [
		x^2 - 2*t2*x + t1*t2 - t1 + t2,
		-x^2 + 2*t2*x - t0*t2,
		(t0 - t1 - 1)*x^2 + 2*t1*x - t0*t1 ]
		where t0,t1,t2 := Explode(Eltseq(xx_full));
	    assert &and[ Valuation(Evaluate(Richelot[i],uu[i])) gt 0 : i in [1..3] ];
	    uu_full := [ HenselLift(Richelot[i],uu[i]) : i in [1..3] ];
	    yy_full := VS![ GaloisImage(xx_full[i],r) : i in [1..3] ];
	    zz_full := Eltseq(xx_full) cat Eltseq(uu_full) cat Eltseq(yy_full);
	    if &and[ Evaluate(f,zz_full) eq 0 : f in Psi ] then
		Include(~xx_sols_new,xx_full);
	    end if;
	end for;
	xx_sols_SS join:= xx_sols_new;
	vprintf CanonicalLift, 2 : "Found %o new solutions.\n", #xx_sols_new;
	vprintf CanonicalLift, 2 : "Current total solutions %o.\n", #xx_sols_SS;
    end for;
    vprintf CanonicalLift : "Total number of solutions: %o", #xx_sols_SS;
    if #xx_sols_SS gt 1 then
	vprintf CanonicalLift : " (valuations: %o)\n",
	    { Min([ Valuation(c) : c in Eltseq(x-y) ]) : x, y in xx_sols_SS | x ne y };
    else
	vprint CanonicalLift : "";
    end if;
    return xx_sols_SS;
end function;

intrinsic CanonicalLiftRosenhainInvariants(
    xx::SeqEnum[FldFinElt],prec::RngIntElt : 
    UseCyclotomicExtension := false, ExtraPrecision := 1) -> SeqEnum
    {The canonical lift of Rosenhain modular invariants xx = [t0,t1,t2] with
    respect to Richelot correspondence with [t0^q,t1^q,t2^q] where q = p^r.}
    p := Characteristic(Universe(xx));
    require p ne 2 :
	"Argument 1 must be defined over a finite field of odd characteristic.";
    return CanonicalLiftRosenhainInvariants(xx,1,prec : 
	UseCyclotomicExtension := UseCyclotomicExtension,
	ExtraPrecision := ExtraPrecision);
end intrinsic;    


intrinsic CanonicalLiftRosenhainInvariants(
    xx::SeqEnum[FldFinElt],r::RngIntElt,prec::RngIntElt : 
    UseCyclotomicExtension := false, ExtraPrecision := 1) -> SeqEnum
    {The canonical lift of Rosenhain modular invariants xx = [t0,t1,t2] with
    respect to Richelot correspondence with [t0^q,t1^q,t2^q] where q = p^r.}
    
    FF := Universe(xx);
    p := Characteristic(FF);
    require p ne 2 : "Argument 1 must be defined over a finite field of odd characteristic.";
    require r eq 1 : "Argument 2 must presently be 1.";
    yy := [ t^p^r : t in xx ]; 
    bool, Psi, uu, gg := ExistsModularRichelotTransformation(xx,yy);
    // assert &and[ Evaluate(Psi[i],xx cat uu cat yy) eq 0 : i in [1..3] ];
    require bool : "Arguments 1 must admit a modular Richelot isogeny.";

    F6<T0,T1,T2,U0,U1,U2,S0,S1,S2> := Universe(Psi);
    Phi := [
	U0^2 - 2*T2*U0 + T1*T2 - T1 + T2,
	-(U1^2 - 2*T2*U1 + T0*T2),
	(T0 - T1 - 1)*U2^2 + 2*T1*U2 - T0*T1 ];
    DPsi := [ [ Derivative(f,i) : f in Psi ] : i in [1..9] ];
    DPhi := [ [ Derivative(f,i) : f in Phi ] : i in [1..6] ];

    RR := pAdicQuotientRing(p,prec+ExtraPrecision);
    n := Degree(FF);
    if UseCyclotomicExtension then
	SS<w> := UnramifiedCyclotomicExtension(RR,n);
    else
	SS<w> := UnramifiedExtension(RR,n);
    end if;
    xx := [ SS!Eltseq(ti) : ti in xx ];
    Richelot := [
	Polynomial([t1*t2-t1+t2, -2*t2, 1]),
	Polynomial([-t0*t2, 2*t2, -1]),
	Polynomial([-t0*t1, 2*t1, (t0-t1-1) ]) ]
	where t0,t1,t2 := Explode(Eltseq(xx));
    uu := [ HenselLift(Richelot[i],SS!Eltseq(uu[i])) : i in [1..3] ];
    tt_set := NewtonAGMLifts(xx,uu,r,Phi,Psi,DPhi,DPsi : ExtraPrecision := ExtraPrecision);
    if ExtraPrecision gt 0 then
	S1 := ChangePrecision(SS,prec);
	tt_set := { ChangeUniverse(Eltseq(tt),S1) : tt in tt_set };
    end if;
    return Representative(tt_set);
end intrinsic;
