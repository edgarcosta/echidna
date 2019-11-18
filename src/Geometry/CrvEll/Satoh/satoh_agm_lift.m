//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//                     SATOH AGM Lifting Algorithms                         //
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

function NewtonAGMLift(j1,Phi,DxPhi,DyPhi)
    SS := Parent(j1);
    p := ResidueCharacteristic(SS);
    prec := Precision(SS);
    if prec eq 1 then return j1; end if;
    prec1 := (prec+1) div 2;
    
    vprintf CanonicalLift : "REDUCING TO LOWER PRECISION: %o\n", prec1;

    S1 := ChangePrecision(SS,prec1); AssignNames(~S1,["t"]);
    j1_half_S1 := NewtonAGMLift(S1!j1,Phi,DxPhi,DyPhi);
    j2_half_S1 := FrobeniusImage(j1_half_S1);

    vprintf CanonicalLift : "LIFTED HALFWAY TO PRECISION: %o\n", prec1;
    
    Dy := Evaluate(DyPhi,[j1_half_S1,j2_half_S1]); // != u mod p
    vprint CanonicalLift, 2: "Valuation(Dy) =", Valuation(Dy);
    Dx := Evaluate(DxPhi,[j1_half_S1,j2_half_S1]); // == 0 mod p
    vprint CanonicalLift, 2: "Valuation(Dx) =", Valuation(Dx);

    j1_half_SS := SS!j1_half_S1;
    j2_half_SS := FrobeniusImage(j1_half_SS);
    cc := S1!(Evaluate(Phi,[j1_half_SS,j2_half_SS]) div p^prec1);
    vprint CanonicalLift, 2: "Valuation(cc) =", Valuation(cc);

    tyme := Cputime();
    delta_1 := ArtinSchreierRoot([Dy,Dx,cc]);
    vprint CanonicalLift : "Artin-Schreier root time:", Cputime(tyme);
    delta_2 := FrobeniusImage(delta_1);
    return j1_half_SS + p^prec1*(SS!delta_1);
end function;

intrinsic SatohAGMLift(j::FldFinElt,prec::RngIntElt) -> RngPadResExtElt
    {Return the canonical lift of the j-invariant j.}
    F := Parent(j);
    n := Degree(F);
    p := Characteristic(F);
    require n ge 3 or IsOrdinary(EllipticCurveFromjInvariant(j)) : 
	"Argument 1 must be an ordinary j-invariant.";
    R := pAdicQuotientRing(p,prec);
    Phi := ClassicalModularPolynomial(p);
    if n eq 1 then
	x := PolynomialRing(R).1;
	phi := Derivative(Evaluate(Phi,[x,x]));
	return HenselLift(phi,R!j);
    end if;
    S := UnramifiedExtension(R,n);
    if n eq 2 then
	// This might as well pre-compute the class polynomial and 
	// Hensel lift the result than use modular polynomials.
	Phi2 := ClassicalModularPolynomial(p^2);
	x := PolynomialRing(IntegerRing()).1;
	P := PolynomialRing(S);
	phi := P!Derivative(Evaluate(Phi2,[x,x]) div p);
	return HenselLift(phi,S!j);
    end if;
    DxPhi := Derivative(Phi,1);
    DyPhi := Derivative(Phi,2);
    return NewtonAGMLift(S!j,Phi,DxPhi,DyPhi);
end intrinsic;

