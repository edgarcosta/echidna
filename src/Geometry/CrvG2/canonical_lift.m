//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare verbose CanonicalLift, 4;

//////////////////////////////////////////////////////////////////////////////

/*
Sample usage:

chi := PZ!(x^4 - x^3 - 43*x^2 - 27*x + 729);
JJ_seq := OrdinaryIgusaInvariants(DBOC,chi);
C := HyperellipticCurveFromIgusaInvariants(JJ_seq[1]);
JJ := CanonicalLiftAbsoluteIgusaInvariants(C,1024);

K := NumberField(chi);
K_r := QuarticCMReflexField(K);
JJ_H := HilbertClassFieldReconstruction(JJ[[1,2,4]],K_r);

[ MinimalPolynomial(ji) : ji in JJ_H ];

*/

function UnramifiedImages(JJ,Kp)
    ZZ := Integers();
    S := Universe(JJ);
    fS := PolynomialRing(ZZ)!DefiningPolynomial(S);
    kp, mp := ResidueClassField(Kp);
    rp := Roots(Polynomial([ mp(c) : c in Eltseq(fS) ]))[1][1]; 
    xp := HenselLift(PolynomialRing(Kp)!fS, rp@@mp);
    return [ Evaluate(Polynomial([ ZZ!c : c in Eltseq(x)]),xp) : x in JJ ];
end function;

function UnramifiedDescent(JJ,d1 : pAdicDescentRing := false)
    /*
    Given a sequence of elements over in an unramified p-adic ring
    of degree d1*d2, which are defined over the degree d1 subring,
    reconstructs them over a degree d1 ring.
    */
    S := Universe(JJ);
    fS := DefiningPolynomial(S);
    d2 := Degree(S) div d1;
    if ISA(Type(pAdicDescentRing),Rng) then
	S1 := pAdicDescentRing;
	R1 := BaseRing(S1);
	assert Degree(S1) eq d1;
    else
	R1 := BaseRing(S);
	d2 := Degree(S) div d1;
	S1 := UnramifiedExtension(R1,d1);
    end if;
    S2 := UnramifiedExtension(S1,d2);
    k2, m2 := ResidueClassField(S2);
    r2 := Roots(Polynomial([ m2(c) : c in Eltseq(fS) ]))[1][1]; 
    x2 := HenselLift(PolynomialRing(S2)!fS, r2@@m2);
    JJ_2 := [ Evaluate(Polynomial(ChangeUniverse(Eltseq(x),R1)),x2) : x in JJ ];
    bool, JJ_1 := CanChangeUniverse(JJ_2,S1);
    if not bool then
	vals := &cat[ [ Valuation(c) : c in Eltseq(j)[[2..d2]] ] : j in JJ_2 ];
	minv := Min(vals);
	vprintf CanonicalLift, 2 : 
	    "Reducing precision from %o to %o\,", Precision(S), minv;
	S2 := ChangePrecision(S2,minv);
	S1 := BaseRing(S2);
	JJ_1 := [ S1!S2!j : j in JJ_2 ];
    end if;
    return JJ_1;
end function;

intrinsic CanonicalLiftAbsoluteIgusaInvariants(
    C::CrvHyp[FldFin],prec::RngIntElt : pAdicLiftingRing := false) -> SeqEnum
    {Returns the canonical lifts of the absolute igusa invariants j1, j2, j4.}
    FF := BaseRing(C);
    p := Characteristic(FF);
    require Genus(C) eq 2 : "Argument 1 must have genus 2.";
    require p in {2,3} :
	"Base ring of argument 1 must have charactristic 2 or 3.";
    if p eq 2 then
	tt := Level2ThetaCurveCoefficientsOverSplittingField(C);
	xx := AffineLevel2ThetaNullPointFromLevel2ThetaCurveCoefficients(tt);
	XX := CanonicalLiftAffineLevel2ThetaNullPoint(xx,prec+16);
	// Take the lifting ring, and create a non-quotient ring which
	// has a well-defined field of fractions:
	S1 := ChangePrecision(Universe(XX),prec);
	RR := pAdicRing(2,prec+16);
	SS := UnramifiedExtension(RR,Degree(S1));
	//
	XX := [ SS!Eltseq(xi) : xi in XX ];
	AA := Level2ThetaNullPointFromAffineLevel2ThetaNullPoint(XX);
	TT := Level2ThetaNullPointToRosenhainInvariants(AA);
	JJ := RosenhainToAbsoluteIgusaInvariants(TT);
	JJ := [ S1!Eltseq(ji) : ji in JJ[[1,2,4]] ];
    else
	vprint CanonicalLift : "Base degree:", Degree(FF);
	ee := RosenhainInvariantsOverSplittingField(C);
	vprint CanonicalLift : "Rosenhain degree:", Degree(Universe(ee));
	t2 := Level2ThetaNullPointFromRosenhainInvariantsOverSplittingField(ee);
	vprint CanonicalLift : "2-Theta null degree:", Degree(Universe(t2));
	t4 := Level4ThetaNullPointFromLevel2ThetaNullPointOverSplittingField(t2);
	vprint CanonicalLift : "4-Theta null degree:", Degree(Universe(t4));
	T4 := CanonicalLiftLevel4ThetaNullPoint(t4,prec);
	EE := Level4ThetaNullPointToRosenhainInvariants(T4);
	JJ := RosenhainToAbsoluteIgusaInvariants(EE)[[1,2,4]];
    end if;
    return UnramifiedDescent(JJ,Degree(FF) : pAdicDescentRing := pAdicLiftingRing);
end intrinsic;

/*
function RationalReconstruction(JJ,pp)
    // INPUT:
    // JJ is a sequence of j-invariants, H/K_reflex the Hilbert class
    // field in which they reside, and pp a place...
    // OUTPUT:
    // The sequence of j-invariants as elements of H.
    // N.B. The output is subject to a choice of prime.
    p := Generator(Integers() meet pp);
    OH := Order(pp);
    OH_p, mp := Completion(OH, pp);
    prec := Precision(Universe(JJ))-8;
    OH_p`DefaultPrecision := prec;
    JJ_p := UnramifiedImages(JJ,OH_p);
    Env := ReconstructionEnvironment(pp, prec);
    return [ Reconstruct(Order(pp)!ji@@mp, Env) : ji in JJ_p ];
end function;

intrinsic HilbertClassFieldReconstruction(
    JJ::SeqEnum[RngPadResExtElt],K_r::FldNum) -> SeqEnum
    {Intended use: JJ is a sequence of absolute Igusa invariants,
    and K_r is the CM reflex field.  This finds a reconstruction
    to p-adic precision 'prec' with respect to some prime of
    completion.}
    S := Universe(JJ);
    deg := Degree(S);
    prec := Precision(S);
    p := ResidueCharacteristic(S); 
    tyme := Cputime();
    H := AbsoluteField(HilbertClassField(K_r));
    vprint CanonicalLift : "Hilbert class field time:", Cputime(tyme);
    dcmp := Decomposition(H, p);
    plcs := [ Ideal(pp[1]) : pp in dcmp | Degree(pp[1]) eq deg ];
    require #plcs gt 0 :
	"Argument 1 can not defined over Hilbert class field.";
    vprint CanonicalLift : Sprintf("There are %o primes.",#plcs);
    return RationalReconstruction(JJ,plcs[1]);
end intrinsic;

intrinsic RayClassFieldReconstruction(
    JJ::SeqEnum[RngPadResExtElt],M::RngOrdIdl) -> SeqEnum
    {Intended use: JJ is a sequence of absolute Igusa invariants,
    and M is an ideal of the CM reflex field.  This finds a
    reconstruction (to given p-adic precision) with respect to
    some prime of completion.}
    S := Universe(JJ);
    deg := Degree(S);
    prec := Precision(S);
    p := ResidueCharacteristic(S); 
    tyme := Cputime();
    H := AbsoluteField(NumberField(RayClassField(M)));
    vprint CanonicalLift : "Ray class field time:", Cputime(tyme);
    dcmp := Decomposition(H, p);
    plcs := [ Ideal(pp[1]) : pp in dcmp | Degree(pp[1]) mod deg eq 0 ];
    require #plcs gt 0 :
	"Argument 1 can not defined over ray class field.";
    vprint CanonicalLift : Sprintf("There are %o primes.",#plcs);
    return RationalReconstruction(JJ,plcs[1]);
end intrinsic;
*/
