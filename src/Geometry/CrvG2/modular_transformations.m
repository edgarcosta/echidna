//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//   Transformations between moduli of genus 2 curves.                      //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


//////////////////////////////////////////////////////////////////////////////
// Projective normalization
//////////////////////////////////////////////////////////////////////////////

function ProjectiveNormalization(v)
    bool, u1 := IsInvertible(v[1]); assert bool;
    return [ ci * u1 : ci in v ];
end function;

//////////////////////////////////////////////////////////////////////////////
// Rosenhain invariants
//////////////////////////////////////////////////////////////////////////////

intrinsic ExistsRosenhainInvariants(C::CrvHyp) -> SeqEnum
    {}
    require Characteristic(BaseRing(C)) ne 2 : 
        "Argument must be defined over a finite field of odd characteristic.";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    f, h := HyperellipticPolynomials(SimplifiedModel(C));
    if h ne 0 then
	f +:= h^2/4;
    end if;
    ee := [ ei[1] : ei in Roots(f) ];
    if #ee ne Degree(f) then
        return false, _;
    elif #ee eq 5 then
        return true, [ (ee[i]-ee[5])/(ee[4]-ee[5]) : i in [1..3] ];
    elif Degree(f) eq 6 then
        return true, [ (ee[i]-ee[5])*(ee[4]-ee[6])/
        ((ee[i]-ee[6])*(ee[4]-ee[5])) : i in [1..3] ];
    end if;
end intrinsic;

intrinsic RosenhainInvariants(C::CrvHyp) -> SeqEnum
    {}
    require Characteristic(BaseRing(C)) ne 2 : 
        "Argument must be defined over a finite field of odd characteristic.";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    bool, ee := ExistsRosenhainInvariants(C);
    require bool :
        "Argument must have split Weierstrass locus over base field.";
    return ee;
end intrinsic;

intrinsic RosenhainInvariantsOverSplittingField(C::CrvHyp[Fld]) -> SeqEnum
    {}
    require Type(BaseRing(C)) in {FldFin,FldRat,FldQuad,FldCyc,FldNum} : 
        "Argument must be defined over a finite field or number field.";
    require Characteristic(BaseRing(C)) ne 2 : 
        "Argument must be defined over a finite field of odd characteristic.";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    f, h := HyperellipticPolynomials(SimplifiedModel(C));
    if h ne 0 then
	f +:= h^2/4;
    end if;
    P := PolynomialRing(SplittingField(f));
    ee := [ ei[1] : ei in Roots(P!f) ];
    if #ee eq 5 then
        return [ (ee[i]-ee[5])/(ee[4]-ee[5]) : i in [1..3] ];
    elif Degree(f) eq 6 then
        return [ (ee[i]-ee[5])*(ee[4]-ee[6])/
        ((ee[i]-ee[6])*(ee[4]-ee[5])) : i in [1..3] ];
    end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
// Lifting from Rosenhain invariants to theta constants.                   //
/////////////////////////////////////////////////////////////////////////////

/*
We need a naming convention to determine what theta constants are being
returned.  These algorithms compute a full set of 4-theta constants (a_ij),
after which the projectively normalised (a_2i2j) constants are returned.

We may also want the theta constants (b_ij) for a 2-theta structure and
the full sequence (a_ij) of 4-theta constants.
*/

intrinsic ExistsLevel2ThetaNullPoint(C::CrvHyp) -> ModTupRngElt
    {The 2-torsion part of the theta null point of the Jacobian of the curve C
    is computed. Note that this requires the choice of a 4-theta structure.}

    R := BaseRing(C);
    require Characteristic(R) ne 2 : 
        "Argument must be defined over a finite field of odd characteristic.";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    bool, ee := ExistsRosenhainInvariants(C);
    if not bool then return bool, _; end if;
    return ExistsLevel2ThetaNullPointFromRosenhainInvariants(ee);
end intrinsic;

intrinsic Level2ThetaNullPoint(C::CrvHyp) -> ModTupRngElt
    {The 2-torsion part of the theta null point of the Jacobian of the curve C
    is computed. Note that this requires the choice of a 4-theta structure.}

    R := BaseRing(C);
    require Characteristic(R) ne 2 : 
        "Argument must be defined over a finite field of odd characteristic.";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    bool, ee := ExistsRosenhainInvariants(C);
    if not bool then return bool, _; end if;
    require bool:
        "Argument must have split Weierstrass locus over base field.";

    if not bool then return bool, _; end if;
    require bool:
        "Argument must have split Weierstrass locus over base field.";
    bool, tt := ExistsLevel2ThetaNullPointFromRosenhainInvariants(ee);
    require bool:
        "Argument must have 2-theta structure over its base field.";
    return tt;
end intrinsic;

intrinsic Level2ThetaNullPointOverSplittingField(C::CrvHyp[FldFin] :
    Normalize := false) -> ModTupRngElt
    {The 2-torsion part of the theta null point of the Jacobian of the curve H
    is computed. Note that this requires the choice of a 4-theta structure.}
    require Characteristic(BaseRing(C)) ne 2 : 
        "Argument must be defined over a finite field of odd characteristic.";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    ee := RosenhainInvariantsOverSplittingField(C);
    return Level2ThetaNullPointFromRosenhainInvariantsOverSplittingField(ee);
end intrinsic;

intrinsic IsogenousLevel2ThetaNullPointOverSplittingField(C::CrvHyp[FldFin]) -> SeqEnum
    {The 2-torsion part of a level 4 theta null point for the Jacobian
    of the curve C is computed, which is a level 2 theta null point for
    the (2,2)-isogenous abelian variety.}
    require Characteristic(BaseRing(C)) ne 2 :
	"Argument must be defined over a finite field of odd characteristic.";
    require Genus(C) eq 2 : "Argument must have genus 2.";
    ee := RosenhainInvariantsOverSplittingField(C);
    FF := Universe(ee);
    e1, e2, e3 := Explode(ee); e4 := FF!1; e5 := FF!0;
    X := PolynomialRing(FF).1;
    // Splitting field for a polynomials over a finite field takes a set,
    // while the signature for sequences creates a number field extension. 
    KK := SplittingField({
	X^4 - ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5)),
	X^4 - ((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5)),
	X^2 - ((e1-e2)*(e1-e4)*(e2-e5)*(e3-e4))/((e1-e3)*(e1-e5)*(e2-e4)*(e3-e5)) });
    t0 := 1;
    t1 := Sqrt(Sqrt(KK!((e1-e4)*(e2-e5)*(e3-e4)))/((e1-e5)*(e2-e4)*(e3-e5)));
    t2 := Sqrt(Sqrt(KK!((e1-e2)*(e1-e4)))/((e1-e3)*(e1-e5)));
    t3 := Sqrt(Sqrt(KK!((e1-e2)*(e2-e5)*(e3-e4)))/((e1-e3)*(e2-e4)*(e3-e5)));
    /*
    Non-normalized 2-torsion part:
      t0 = (f12*f14*f25*f34)
      t1 = (f12*f15*f24*f35)
      t2 = (f13*f15*f25*f34)
      t3 = (f13*f14*f24*f35)
    Normalization satisfies
      (t1/t0)*(t2/t0)*(t3/t0) = 
        (f15*f24*f35)/(f14*f25*f34) *
        (f13*f15)/(f12*f14) *
        (f13*f24*f35)/(f12*f25*f34) = 
        ((f13*f15*f24*f35)/(f12*f14*f25*f34))^2
    where fij is a 4-th root of 1/(ei-ej).
    */
    return [t0,t1,t2,t3]; 
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
// Extraction of a set of theta constants from Rosenhain invariants.       //
/////////////////////////////////////////////////////////////////////////////

intrinsic ExistsLevel2ThetaNullPointFromRosenhainInvariants(
    ee::SeqEnum[RngElt] : Check := true, Normalize := false) -> SeqEnum
    {True if there exists a 2-theta null point for the Jacobian of a curve
    with Rosenhain invariants ee = [e1,e2,e3] over its field of definition,
    and if so returns one.} 

    FF := Universe(ee);
    require Characteristic(FF) ne 2:
        "Argument must be defined over a finite field of odd characteristic.";
    require #ee in {3,4} :
        "Argument must be a sequence of three or four Rosenhain invariants.";
    ee_five := #ee eq 4 select [ FF | 0 ] cat ee else [ FF | 0, 1 ] cat ee;
    require #SequenceToSet(ee_five) eq 5 :
        "Argument must consist of distinct elements not equal to 0 or 1.";
    e1, e2, e3, e4, e5 := Explode(ee_five);
    /*
    u00 = 1
    u10^2 = ((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5))
    u11^2 = ((e1-e2)*(e2-e5)*(e3-e4))/((e1-e3)*(e2-e4)*(e3-e5))
    u01 = ((e1-e3)/(e1-e2))*u10*u11, hence, 
    u01^2 == ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5))
    */
    u00 := 1;
    bool, u10 := IsSquare(((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5))); 
    if not bool then return false, _; end if;
    bool, u11 := IsSquare(((e1-e2)*(e2-e5)*(e3-e4))/((e1-e3)*(e2-e4)*(e3-e5)));
    if not bool then return false, _; end if;
    u01 := (e1-e3)/(e1-e2)*u10*u11;
    if Check then
	assert u01^2 eq ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5));
    end if;
    /*
    (y00+y01+y10+y11)^2 = t*(u00+u01+u10+u11)
    (y00-y01+y10-y11)^2 = t*(u00-u01+u10-u11)
    (y00+y01-y10-y11)^2 = t*(u00+u01-u10-u11)
    (y00-y01-y10+y11)^2 = t*(u00-u01-u10+u11)
    */
    lam := u00+u01+u10+u11;
    if lam ne 0 then
	r00 := 1;
    else
	r00 := 0;
	lam := u00-u01+u10-u11;
    end if;
    lam_inv := lam^-1;
    bool, r01 := IsSquare((u00-u01+u10-u11)*lam_inv);
    if not bool then return false, _; end if;
    bool, r10 := IsSquare((u00+u01-u10-u11)*lam_inv);
    if not bool then return false, _; end if;
    if r00 eq 0 or r01 eq 0 or r10 eq 0 then
	bool, r11 := IsSquare((u00-u01-u10+u11)*lam_inv);
	if not bool then return false, _; end if;
    else
	r11 := r00*r01/r10*((e1-e4)*u11-(e1-e2)*u01)/((e1-e4)*u11+(e1-e2)*u01);
    end if;
    if Check then
	assert r11^2 eq (u00-u01-u10+u11)*lam_inv;
    end if;
    y00 := (r00 + r01 + r10 + r11)/4;
    y01 := (r00 - r01 + r10 - r11)/4;
    y10 := (r00 + r01 - r10 - r11)/4;
    y11 := (r00 - r01 - r10 + r11)/4;
    yy := [ y00, y01, y10, y11 ];
    if Check then
	ee_chck := Level2ThetaNullPointToRosenhainInvariants([y00,y01,y10,y11]);
	assert [(e1-e3)/(e1-e2),(e1-e4)/(e1-e2),(e1-e5)/(e1-e2)] eq ee_chck;
    end if;
    if Normalize then
	yy := [ yi*uu : yi in yy] where uu := y00^-1;
    end if;
    return true, yy;
end intrinsic;

intrinsic Level2ThetaNullPointFromRosenhainInvariants(
    ee::SeqEnum[RngElt] : Check := true, Normalize := false) -> SeqEnum
    {The 2-theta null point of the Jacobian of a curve with Rosenhain invariants
    ee = [e1,e2,e3] or [e0,e1,e2,e3] over its field of definition.}
    FF := Universe(ee); 
    require Characteristic(FF) ne 2:
        "Argument must be defined over a finite field of odd characteristic.";
    require #ee in {3,4} :
        "Argument must be a sequence of three or four Rosenhain invariants.";
    ee_five := #ee eq 4 select [ FF | 0 ] cat ee else [ FF | 0, 1 ] cat ee;
    require #SequenceToSet(ee_five) eq 5 :
        "Argument must consist of distinct elements not equal to 0 or 1.";
    bool, tt := ExistsLevel2ThetaNullPointFromRosenhainInvariants(ee :
	Check := Check, Normalize := Normalize);
    require bool : "Argument must admit a 2-theta structure.";
    return tt;
end intrinsic;

function twoAdicExtensionRecursion(A,B)
    /*
    Construct an 2-adic extension KK field containing a root of X^2 + A*X + B.
    INPUT: A,B such that val(B) is 0 or 1 and val(B) <= val(A) < val(2).
    OUTPUT: KK, s such that s^2 + A*s + B = 0.
    */
    KK := Parent(B); 
    p := UniformizingElement(KK);
    n0 := Valuation(B);
    q0 := n0 eq 0 select 1 else p^(n0 div 2);
    A0 := A/q0; 
    B0 := B/q0^2; 
    print "  [val(A),val(B)]:", [ Valuation(A), Valuation(B) ];
    assert Valuation(B0) in {0,1};
    assert Valuation(A0) ge Valuation(B0);
    if Valuation(B0) eq 1 then
	// Eisenstein extension:
	X := PolynomialRing(KK).1;
	LL := ext< KK | X^2 + A0*X + B0 >;
	//print "  Ramified: Precision(KK)", Precision(KK) div RamificationDegree(KK,pAdicField(2));
	//print "  Ramified: Precision(LL)", Precision(LL) div RamificationDegree(LL,pAdicField(2));
	return LL, LL.1 * q0;
    elif Valuation(A0) eq 0 then
	// Unramified extension (possibly trivial):
	X := PolynomialRing(KK).1;
	kk, pi := ResidueClassField(RingOfIntegers(KK));
	a0 := pi(A0); b0 := pi(B0);
	x := PolynomialRing(kk).1;
	rts := Roots(x^2 + a0*x + b0);
	if #rts gt 0 then
	    s0 := KK!(rts[1][1]@@pi);
	    s1 := HenselLift(X^2 + A0*X + B0,s0,Precision(KK));
	    return KK, s1 * q0;
	else
	    LL := ext< KK | X^2 + A0*X + B0 >;
	    //print "Unramified: Precision(KK)", Precision(KK) div RamificationDegree(KK,pAdicField(2));
	    //print "Unramified: Precision(LL)", Precision(LL) div RamificationDegree(LL,pAdicField(2));
	    return LL, LL.1 * q0;
	end if;
    else
	// Recursion (here 0 = val(B0) < val(A0)).
	kk, pi := ResidueClassField(RingOfIntegers(KK));
	s0 := KK!(Sqrt(pi(B0))@@pi);
	A1 := Expand(2*s0+A0);
	B1 := Expand(s0^2+A0*s0+B0);
	n1 := Valuation(B1);
	q1 := n1 eq 0 select 1 else p^(n1 div 2);
	A1 /:= q1;
	B1 /:= q1^2;
	LL, s1 := twoAdicExtensionRecursion(A1,B1);
	//print " Recursion: Precision(KK)", Precision(KK) div RamificationDegree(KK,pAdicField(2));
	//print " Recursion: Precision(LL)", Precision(LL) div RamificationDegree(LL,pAdicField(2));
	return LL, (s0 + s1 * q1) * q0;
    end if;
end function;

function twoAdicExtensionSquareRoot(c)
    /*
    Construct an 2-adic extension KK field containing a square root of c.    
    */
    KK := Parent(c);
    LL, sqrtc := twoAdicExtensionRecursion(KK!0,-c);
    // This may not be necessary...
    sqrtc := HenselLift(X^2-c,sqrtc,Precision(LL)) where X := PolynomialRing(LL).1;
    print "  Precision(sqrtc):", RealField(8)!Precision(sqrtc)/Valuation(LL!2);
    print "    val(sqrtc^2-c):", RealField(8)!Valuation(Expand(sqrtc^2-c))/Valuation(LL!2);
    return LL, sqrtc;
end function;

intrinsic Level2ThetaNullPointFromRosenhainInvariantsOverSplittingField(
    ee::SeqEnum[FldElt] : Check := true, Normalize := false) -> SeqEnum
    {Returns a 2-theta null point for the Jacobian of a curve with
    Rosenhain invariants ee = [e1,e2,e3] over its field of definition,
    if one exists.} 

    KK := Universe(ee);
    require Characteristic(KK) ne 2:
        "Argument must be defined over a finite field of odd characteristic.";
    require #ee in {3,4} :
        "Argument must be a sequence of three or four Rosenhain invariants.";
    ee_five := #ee eq 4 select [ KK | 0 ] cat ee else [ KK | 0, 1 ] cat ee;
    require #SequenceToSet(ee_five) eq 5 :
        "Argument must consist of distinct elements not equal to 0 or 1.";
    e1, e2, e3, e4, e5 := Explode(ee_five);
    /*
    u00 = 1
    u10^2 = ((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5))
    u11^2 = ((e1-e2)*(e2-e5)*(e3-e4))/((e1-e3)*(e2-e4)*(e3-e5))
    u01 = ((e1-e3)/(e1-e2))*u10*u11, hence, 
    u01^2 == ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5))
    */
    c10 := ((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5));
    c11 := ((e1-e2)*(e2-e5)*(e3-e4))/((e1-e3)*(e2-e4)*(e3-e5));
    u00 := 1;
    bool, u10 := IsSquare(KK!c10);
    if not bool then
	if Type(KK) eq FldPad and Prime(KK) eq 2 then
	    KK, u10 := twoAdicExtensionSquareRoot(c10);
	else
	    KK := ext< KK | X^2-c10 > where X := PolynomialRing(KK).1;
	    u10 := KK.1;
	end if;
    end if;
    bool, u11 := IsSquare(KK!c11);
    if not bool then
	if Type(KK) eq FldPad and Prime(KK) eq 2 then
	    KK, u11 := twoAdicExtensionSquareRoot(c11);
	else
	    KK := ext< KK | X^2-c11 > where X := PolynomialRing(KK).1;
	    u11 := KK.1;
	end if;
    end if;
    u01 := ((e1-e3)/(e1-e2))*u10*u11;
    if Check then
	if Type(KK) eq FldPad then
	    assert Valuation(u01^2-((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5))) gt 8;
	else
	    assert u01^2 eq ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5));
	end if;
    end if;
    /*
    (y00+y01+y10+y11)^2 = t*(u00+u01+u10+u11)
    (y00-y01+y10-y11)^2 = t*(u00-u01+u10-u11)
    (y00+y01-y10-y11)^2 = t*(u00+u01-u10-u11)
    (y00-y01-y10+y11)^2 = t*(u00-u01-u10+u11)
    */
    lam := u00+u01+u10+u11;
    if lam ne 0 then
	r00 := 1;
    else
	r00 := 0;
	lam := u00-u01+u10-u11;
    end if;
    lam_inv := lam^-1;
    s01 := (u00-u01+u10-u11)*lam_inv;
    s10 := (u00+u01-u10-u11)*lam_inv;
    s11 := (u00-u01-u10+u11)*lam_inv;
    // 
    r00 := KK!r00; 
    bool, r01 := IsSquare(KK!s01);
    if not bool then
	if Type(KK) eq FldPad and Prime(KK) eq 2 then
	    KK, r01 := twoAdicExtensionSquareRoot(s01);
	else
	    KK := ext< KK | X^2-s01 > where X := PolynomialRing(KK).1;
	    r01 := KK.1;
	end if;
    end if;
    bool, r10 := IsSquare(KK!s10);
    if not bool then
	if Type(KK) eq FldPad and Prime(KK) eq 2 then
	    KK, r10 := twoAdicExtensionSquareRoot(s10);
	else
	    KK := ext< KK | X^2-s10 > where X := PolynomialRing(KK).1;
	    r10 := KK.1;
	end if;
    end if;
    if r00 eq 0 or r01 eq 0 or r10 eq 0 then
	bool, r11 := IsSquare(KK!s11);
	if not bool then
	    if Type(KK) eq FldPad and Prime(KK) eq 2 then
		KK, r11 := twoAdicExtensionSquareRoot(s11);
	    else
		KK := ext< KK | X^2-s11 > where X := PolynomialRing(KK).1;
		r11 := KK.1;
	    end if;
	end if;
    else
	num := ((e1-e4)*u11-(e1-e2)*u01);
	den := ((e1-e4)*u11+(e1-e2)*u01); assert den ne 0;
	r11 := r00*r01/r10*num/den;
    end if;
    if Check then
	if Type(KK) eq FldPad then
	    assert Valuation(r11^2-s11) ge 8;
	else
	    assert r11^2 eq s11;
	end if;
    end if;
    y00 := (r00 + r01 + r10 + r11)/4;
    y01 := (r00 - r01 + r10 - r11)/4;
    y10 := (r00 + r01 - r10 - r11)/4;
    y11 := (r00 - r01 - r10 + r11)/4;
    yy := [ y00, y01, y10, y11 ];
    if Check then
	ee_chck := Level2ThetaNullPointToRosenhainInvariants(yy);
	if Type(KK) eq FldPad then
	    prec := Precision(KK) div 3;
	    assert Valuation((e1-e3)/(e1-e2) - ee_chck[1]) ge prec;
	    assert Valuation((e1-e4)/(e1-e2) - ee_chck[2]) ge prec;
	    assert Valuation((e1-e5)/(e1-e2) - ee_chck[3]) ge prec;
	else
	    assert [(e1-e3)/(e1-e2),(e1-e4)/(e1-e2),(e1-e5)/(e1-e2)] eq ee_chck;
	end if;
    end if;
    if Normalize then
	yy := [ yi*uu : yi in yy] where uu := y00^-1;
    end if;
    return yy;
end intrinsic;

intrinsic ExistsIsogenousLevel2ThetaNullPointFromRosenhainInvariants(
    ee::SeqEnum[RngElt] : Check := true) -> SeqEnum
    {True if there exists a 2-theta null point for the Jacobian of a curve
    with Rosenhain invariants ee = [e1,e2,e3] over its field of definition,
    and if so returns one.} 

    print "Warning: This not not the correct map...";
    FF := Universe(ee);
    require Characteristic(FF) ne 2:
        "Argument must be defined over a finite field of odd characteristic.";
    require #ee in {3,4} :
        "Argument must be a sequence of three or four Rosenhain invariants.";
    ee_five := #ee eq 4 select [ FF | 0 ] cat ee else [ FF | 0, 1 ] cat ee;
    require #SequenceToSet(ee_five) eq 5 :
        "Argument must consist of distinct elements not equal to 0 or 1.";
    e1, e2, e3, e4, e5 := Explode(ee_five);
    /*
    y00^4 = 1
    y10^4 = ((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5))
    y11^4 = ((e1-e2)*(e3-e5)*(e2-e4))/((e1-e2)*(e3-e4)*(e2-e5))
    y01^2 = ((e1-e3)/(e1-e2))*(y10*y11)^2, so that
    y01^4 = ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5))
    */	
    s01_square := (e1-e3)/(e1-e2);
    y10_fourth := ((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5));
    y11_fourth := ((e1-e2)*(e2-e5)*(e3-e4))/((e1-e3)*(e2-e4)*(e3-e5));
    bool, s01 := IsPower(s01_square,2); 
    if not bool then return false, _; end if;
    bool, y10 := IsPower(y10_fourth,4);
    if not bool then return false, _; end if;
    bool, y11 := IsPower(y11_fourth,4);
    if not bool then return false, _; end if;
    y01 := s01*y10*y11;
    if Check then
	y01_fourth := ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5));
	assert y01^4 eq y01_fourth;
    end if;
    return true, [ 1, y01, y10, y11 ];
end intrinsic;

intrinsic IsogenousLevel2ThetaNullPointFromRosenhainInvariantsOverSplittingField(
    ee::SeqEnum[FldElt] : Check := true) -> SeqEnum
    {The 2-torsion part of the 4-theta null point of the Jacobian of a curve
    with Rosenhain invariants ee = [e1,e2,e3], over a splitting field.} 
    print "Warning: This not not the correct map...";
    FF := Universe(ee);
    require Characteristic(FF) ne 2:
        "Argument must be defined over a finite field of odd characteristic.";
    require #ee in {3,4} :
        "Argument must be a sequence of three or four Rosenhain invariants.";
    ee_five := #ee eq 4 select [ FF | 0 ] cat ee else [ FF | 0, 1 ] cat ee;
    require #SequenceToSet(ee_five) eq 5 :
        "Argument must consist of distinct elements not equal to 0 or 1.";
    FF := Universe(ee);
    require Characteristic(FF) ne 2:
        "Argument must be defined over a finite field of odd characteristic.";
    e1,e2,e3,e4,e5 := Explode(ee_five);
    s01_square := (e1-e3)/(e1-e2);
    y10_fourth := ((e1-e2)*(e1-e4))/((e1-e3)*(e1-e5));
    y11_fourth := ((e1-e2)*(e2-e5)*(e3-e4))/((e1-e3)*(e2-e4)*(e3-e5));
    X := PolynomialRing(FF).1;
    KK := SplittingField((X^2-s01_square)*(X^4-y10_fourth)*(X^4-y11_fourth));
    y10 := Sqrt(Sqrt(KK!y10_fourth)); 
    y11 := Sqrt(Sqrt(KK!y11_fourth)); 
    y01 := Sqrt(KK!s01_square)*y10*y11;
    if Check then
	y01_fourth := ((e1-e4)*(e2-e5)*(e3-e4))/((e1-e5)*(e2-e4)*(e3-e5));
	assert y01^4 eq y01_fourth;
    end if;
    return [ 1, y01, y10, y11 ];
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
// Mappings from theta constants to Rosenhain invariants.                  //
/////////////////////////////////////////////////////////////////////////////

intrinsic Level4ThetaNullPointToRosenhainInvariants(xx::SeqEnum[RngElt]) -> SeqEnum
    {Given theta constants [x00,x02,x20,x22,x01,x21,x10,x12,x11,x13],
    returns the associated Rosenhain invariants.}
    yy := Level4ThetaNullPointToLevel2ThetaNullPoint(xx);
    return Level2ThetaNullPointToRosenhainInvariants(yy);
end intrinsic;
    
intrinsic Level4ThetaNullPointTo2IsogenousRosenhainInvariants(xx::SeqEnum[RngElt]) -> SeqEnum
    {Given theta constants [x00,x02,x20,x22,x01,x21,x10,x12,x11,x13],
    returns the associated Rosenhain invariants.}
    zz := Level4ThetaNullPointToIsogenousLevel2ThetaNullPoint(xx);
    return Level2ThetaNullPointToRosenhainInvariants(zz);
end intrinsic;
    
intrinsic Level2ThetaNullPointToRosenhainInvariants(yy::SeqEnum) -> SeqEnum
    {Given theta constants [y00,y01,y10,y11], returns the associated
    Rosenhain invariants.}
    y00, y01, y10, y11 := Explode(yy);
    S00 := y00^2 + y01^2 + y10^2 + y11^2;
    S10 := y00^2 - y01^2 + y10^2 - y11^2;
    U01 := 2*(y00*y01 + y10*y11);
    U10 := 2*(y00*y10 + y01*y11);
    U11 := 2*(y00*y11 + y01*y10);
    V10 := 2*(y00*y10 - y01*y11);
    return [ (S00*U01)/(U10*U11), (S10*U01)/(V10*U11), (S00*S10)/(U10*V10) ];
end intrinsic;
    
//////////////////////////////////////////////////////////////////////////////
// Checking for valid theta null point
//////////////////////////////////////////////////////////////////////////////

intrinsic IsValidLevel4ThetaNullPoint(x::SeqEnum[RngElt]) -> BoolElt
    {True if the given 4-theta null point satisfies the Riemann relations.}
    require #x eq 10 : "Argument must consist of ten elements.";
    if Type(Universe(x)) in {RngPad,RngPadRes,RngPadResExt,FldPad} then
	prec := Precision(Universe(x)) div 3;
	return &and[ Valuation(f) ge prec : f in Level4ThetaNullRiemannRelations(x) ];
    else
	return &and[ f eq 0 : f in Level4ThetaNullRiemannRelations(x) ];
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic Level4ThetaNullCorrespondenceRelations(
    xx::SeqEnum[RngElt],yy::SeqEnum[RngElt],p::RngIntElt) -> SeqEnum
    {Given theta null points (x00:x02:x20:x22:x01:x21:x10:x12:x11:x13)
    and (y00:y02:y20:y22:y01:y21:y10:y12:y11:y13), returns the relations
    of the (p,p)-correspondence which complement the Riemann relations,
    where currently p must be 3.} 
    // CAREFUL : this is only a subset of the full relation set.
    require p eq 3 : "Argument 2 must be the prime 3.";
    require #xx eq 10 and #yy eq 10 :
        "Arguments must consist of ten 4-theta constants.";
    x01, x02, x03, x04, x05, x06, x07, x08, x09, x10 := Explode(xx); 
    y01, y02, y03, y04, y05, y06, y07, y08, y09, y10 := Explode(yy); 
    return [
        x01*y02 + x02*y01 + y03*x04 + x03*y04 - 2*(x05*y05 + x06*y06),
        x01*y03 + x03*y01 + x02*y04 + x04*y02 - 2*(x07*y07 + x08*y08),
        x01*y04 + x04*y01 + x02*y03 + x03*y02 - 2*(x10*y10 + x09*y09) ];
end intrinsic;

intrinsic Level2ThetaNullCorrespondenceRelations(
    xx::SeqEnum[RngElt],yy::SeqEnum[RngElt],p::RngIntElt) -> SeqEnum
    {Given theta null points (x00:x01:x10:x11) and (y00:y01:y10:y11), 
    returns of the relations of the (p,p)-correspondence, where
    currently p must be 2.} 
    require p eq 2 : "Argument 2 must be the prime 2.";
    require #xx eq 4 and #yy eq 4 :
        "Arguments must consist of four 2-theta constants.";
    // b00, b01, b10, b11 := Explode(xx); 
    // a00, a02, a20, a22 := Explode(yy); 
    zz := [ bij^2 : bij in xx ];
    eps := [ [1,1,1,1], [1,-1,1,-1], [1,1,-1,-1], [1,-1,-1,1] ];
    rr := [ &+[ ee[i]*zz[i] : i in [1..4] ] : ee in eps ];
    ss := [ (&+[ ee[i]*yy[i] : i in [1..4] ])^2 : ee in eps ];
    return [ rr[i]*ss[j]-rr[j]*ss[i] : i, j in [1..4] | i lt j ];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic Level4ThetaNullRiemannRelations(x::SeqEnum[RngElt]) -> SeqEnum
    {Given a level 4 theta null point (x00:x02:x20:x22:x01:x21:x10:x12:x11:x13),
    returns the Riemann relations of the space of theta null points; these
    should be zero on a valid level 4 theta null point.}
    require #x eq 10 : "Argument must consist of elements.";
    a00, a02, a20, a22, a01, a21, a10, a12, a11, a13 := Explode(x); 
    X4toX2 := [
        [
        a00^2 + a02^2 + a20^2 + a22^2, // b00*b00
        2*(a01^2 + a21^2), // b00*b01
        2*(a10^2 + a12^2), // b00*b10
        2*(a11^2 + a13^2) // b00*b11
        ],
        [
        (a01^2 + a21^2), // b00*b01
        (a00*a02 + a20*a22), // b01*b01
        2*a11*a13, // b01*b10
        2*a10*a12 // b01*b11
        ],
        [
        (a10^2 + a12^2), // b00*b10
        2*a11*a13, // b01*b10
        (a00*a20 + a02*a22), // b10*b10
        2*a01*a21 // b10*b11
        ],
        [
        (a11^2 + a13^2), // b00*b11
        2*a10*a12, // b01*b11
        2*a01*a21, // b10*b11
        (a00*a22 + a02*a20) // b11*b11
        ]
        ];
    RiemEQs := [ ];
    for i in [1..3] do
        for j in [i+1..4] do
            RiemEQs cat:= [
                X4toX2[i][m]*X4toX2[j][n] -
                X4toX2[i][n]*X4toX2[j][m] : n, m in [1..4] | n lt m ];
        end for;
    end for;
    return RiemEQs;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Maps between different theta moduli spaces
//////////////////////////////////////////////////////////////////////////////

intrinsic Level4ThetaNullPointToLevel2ThetaNullPoint(x::SeqEnum[RngElt] : 
    Normalize := false) -> SeqEnum
    {Given a level-4 theta null point (x00:x02:x20:x22:x01:x21:x10:x12:x11:x13),
    returns the image level-2 theta null point (y00:y01:y10:y11), in the class of
    (x00^2+x02^2+x20^2+x22^2:2*(x01^2+x21^2):2*(x12^2+x10^2):2*(x11^2+x13^2)).}
    require #x eq 10 : "Argument must consist of ten elements.";
    a00, a02, a20, a22, a01, a21, a10, a12, a11, a13 := Explode(x); 
    b00_square := a00^2 + a02^2 + a20^2 + a22^2;
    if b00_square ne 0 then
        tt := [
            b00_square, // b00*b00
            2*(a01^2 + a21^2), // b00*b01
            2*(a12^2 + a10^2), // b00*b10
            2*(a11^2 + a13^2) // b00*b11
            ];
        if Normalize then
            tt := ProjectiveNormalization(tt);
        end if;
        return tt;
    end if;
    // Normalization with respect to the first variable must fail.
    if Normalize then assert false; end if;
    b01_square := a00*a02 + a20*a22;
    if b01_square ne 0 then
        return [
            a01^2 + a21^2, // b00*b01
            b01_square, // b01*b01
            2*a11*a13, // b01*b10
            2*a10*a12 // b01*b11
            ];
    end if;
    b10_square := a00*a20 + a02*a22;
    if b10_square eq 0 then
        return [
            a12^2 + a10^2, // b00*b10
            2*a11*a13, // b01*b10
            b10_square, // b10*b10
            2*a01*a21 // b10*b11
            ];
    end if;
    b11_square := a00*a22 + a02*a20;
    if b11_square ne 0 then
        return [
            a11^2 + a13^2, // b00*b11
            2*a10*a12, // b01*b11
            2*a01*a21, // b10*b11
            b11_square // b11*b11
            ];
    end if;
    assert false;
end intrinsic;

intrinsic Level4ThetaNullPointToIsogenousLevel2ThetaNullPoint(
    xx::SeqEnum[RngElt]) -> SeqEnum
    {Given a level-4 theta null point (x00:x02:x20:x22:x01:x21:x10:x12:x11:x13)
    returns (x00:x02:x20:x22).}
    return xx[[1..4]];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Level 4 theta null points from level 2...
//////////////////////////////////////////////////////////////////////////////

intrinsic ExistsLevel4ThetaNullPointFromLevel2ThetaNullPoint(
    yy::SeqEnum[RngElt] : Check := true, Normalize := false) -> SeqEnum
    {}
    bool, half := IsInvertible(Universe(yy)!2);
    require bool : "Universe of argument must contain an inverse of 2.";
    y00, y01, y10, y11 := Explode(yy);
    zz := [
        y00^2 + y01^2 + y10^2 + y11^2,
        y00^2 - y01^2 + y10^2 - y11^2,
        y00^2 + y01^2 - y10^2 - y11^2,
        y00^2 - y01^2 - y10^2 + y11^2
        ];
    ww := [
        2*(y00*y01 + y10*y11),
        2*(y00*y11 + y01*y10),
        2*(y00*y10 + y01*y11),
        2*(y00*y01 - y10*y11),
        2*(y00*y11 - y01*y10),
        2*(y00*y10 - y01*y11)
        ];
    for i in [1..6] do
	bool, ui := IsInvertible(ww[i]);
        if bool then
            zz := [ ui*zj : zj in zz ];
            ww := [ ui*wj : wj in ww ];
            break i;
        end if;
    end for;
    bool, a01_plus_a21 := IsPower(ww[1],2); 
    if not bool then return false, _; end if;
    bool, a11_plus_a13 := IsPower(ww[2],2); 
    if not bool then return false, _; end if;
    bool, a10_plus_a12 := IsPower(ww[3],2); 
    if not bool then return false, _; end if;
    bool, a01_minu_a21 := IsPower(ww[4],2); 
    if not bool then return false, _; end if;
    bool, a11_minu_a13 := IsPower(ww[5],2); 
    if not bool then return false, _; end if;
    bool, a10_minu_a12 := IsPower(ww[6],2);
    if not bool then return false, _; end if;
    a01 := a01_plus_a21 + a01_minu_a21;
    a21 := a01_plus_a21 - a01_minu_a21;
    a10 := a10_plus_a12 + a10_minu_a12;
    a12 := a10_plus_a12 - a10_minu_a12;
    a11 := a11_plus_a13 + a11_minu_a13;
    a13 := a11_plus_a13 - a11_minu_a13;
    assert a01*a21*(a01^2+a21^2) eq a10*a12*(a10^2+a12^2);
    assert a01*a21*(a01^2+a21^2) eq a11*a13*(a11^2+a13^2);
    bool, u00 := IsPower(zz[1],2); 
    if not bool then return false, _; end if;
    bool, u01 := IsPower(zz[2],2); 
    if not bool then return false, _; end if;
    bool, u10 := IsPower(zz[3],2); 
    if not bool then return false, _; end if;
    bool, u11 := IsPower(zz[4],2);
    if not bool then return false, _; end if;
    a00 := u00 + u01 + u10 + u11;
    a02 := u00 - u01 + u10 - u11;
    a20 := u00 + u01 - u10 - u11;
    a22 := u00 - u01 - u10 + u11;
    xx := [ a00, a02, a20, a22, a01, a21, a10, a12, a11, a13 ];
    if Check then
	assert IsValidLevel4ThetaNullPoint(xx);
    end if;
    if Normalize then
        xx := ProjectiveNormalization(xx);
    end if;
    return true, xx;
end intrinsic;

intrinsic Level4ThetaNullPointFromLevel2ThetaNullPoint(
    tt::SeqEnum[RngElt] : Check := true, Normalize := false) -> SeqEnum
    {Given a level-2 theta null point (y00:y01:y10:y11), returns a level-4
    theta null point (x00:x02:x20:x22:x01:x21:x10:x12:x11:x13), if it exists,
    such that (y00:y01:y10:y11) is in the class of
    (x00^2+x02^2+x20^2+x22^2:2*(x01^2+x21^2):2*(x12^2+x10^2):2*(x11^2+x13^2)).}
    bool, half := IsInvertible(Universe(tt)!2);
    require bool : "Universe of argument must contain an inverse of 2.";
    bool, tt := ExistsLevel4ThetaNullPointFromLevel2ThetaNullPoint(tt : 
	Check := Check, Normalize := Normalize);
    require bool : "Argument does not lift to a 4-theta null point.";
    return tt;
end intrinsic;

intrinsic Level4ThetaNullPointFromLevel2ThetaNullPointOverSplittingField(
    yy::SeqEnum[RngElt] : Check := true, Normalize := false) -> SeqEnum
    {Given a level-2 theta null point (y00:y01:y10:y11), returns a level-4
    theta null point (x00:x02:x20:x22:x01:x21:x10:x12:x11:x13), over an
    extension ring or field, such that (y00:y01:y10:y11) is in the class of
    (x00^2+x02^2+x20^2+x22^2:2*(x01^2+x21^2):2*(x12^2+x10^2):2*(x11^2+x13^2)).}
    KK := Universe(yy); 
    bool, half := IsInvertible(KK!2);
    require bool : "Universe of argument must contain an inverse of 2.";
    y00, y01, y10, y11 := Explode(yy);
    zz := [
        y00^2 + y01^2 + y10^2 + y11^2,
        y00^2 - y01^2 + y10^2 - y11^2,
        y00^2 + y01^2 - y10^2 - y11^2,
        y00^2 - y01^2 - y10^2 + y11^2
        ];
    ww := [
        2*(y00*y01 + y10*y11),
        2*(y00*y11 + y01*y10),
        2*(y00*y10 + y01*y11),
        2*(y00*y01 - y10*y11),
        2*(y00*y11 - y01*y10),
        2*(y00*y10 - y01*y11)
        ];
    for i in [1..6] do
	bool, ui := IsInvertible(ww[i]);
        if bool then
            zz := [ ui*zj : zj in zz ];
            ww := [ ui*wj : wj in ww ];
            break i;
        end if;
    end for;
    ss := [KK|];
    for i in [1..4] do
	bool, si := IsSquare(zz[i]);
	if not bool then
	    if Type(KK) eq FldPad and Prime(KK) eq 2 then
		KK, si := twoAdicExtensionSquareRoot(zz[i]);
	    else
		KK := ext< KK | X^2-zz[i] > where X := PolynomialRing(KK).1;
		si := KK.1;
	    end if;
	    ChangeUniverse(~zz,KK);
	    ChangeUniverse(~ww,KK);
	    ChangeUniverse(~ss,KK);
	end if;
	Append(~ss,si);
    end for;
    rr := [KK|];
    for i in [1..6] do
	bool, ri := IsSquare(ww[i]);
	if not bool then
	    if Type(KK) eq FldPad and Prime(KK) eq 2 then
		KK, ri := twoAdicExtensionSquareRoot(ww[i]);
	    else
		KK := ext< KK | X^2-ww[i] > where X := PolynomialRing(KK).1;
		ri := KK.1;
	    end if;
	    ChangeUniverse(~ww,KK);
	    ChangeUniverse(~rr,KK);
	end if;
	Append(~rr,ri);
    end for;
    a01_plus_a21 := rr[1]; a01_minu_a21 := rr[4];
    a11_plus_a13 := rr[2]; a11_minu_a13 := rr[5];
    a10_plus_a12 := rr[3]; a10_minu_a12 := rr[6];
    a01 := a01_plus_a21 + a01_minu_a21;
    a21 := a01_plus_a21 - a01_minu_a21;
    a10 := a10_plus_a12 + a10_minu_a12;
    a12 := a10_plus_a12 - a10_minu_a12;
    a11 := a11_plus_a13 + a11_minu_a13;
    a13 := a11_plus_a13 - a11_minu_a13;
    u00, u01, u10, u11 := Explode(ss);
    a00 := u00 + u01 + u10 + u11;
    a02 := u00 - u01 + u10 - u11;
    a20 := u00 + u01 - u10 - u11;
    a22 := u00 - u01 - u10 + u11;
    tt := [ a00, a02, a20, a22, a01, a21, a10, a12, a11, a13 ];
    if Check then
	assert IsValidLevel4ThetaNullPoint(tt);
    end if;
    if Normalize then
        tt := ProjectiveNormalization(tt);
    end if;
    return tt;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function HenselSqrt(x,y0)
    // We could do something more intelligent here, but this 
    // works to extract the one bit of information.
    y := Sqrt(x);
    if Valuation(y-y0) gt 0 then
	return y;
    end if;
    assert Valuation(y+y0) gt 0;
    return -y;
end function;

intrinsic Level4ThetaNullPointFromIsogenousLevel2ThetaNullPointHensel(
    T2::[RngElt],tt::[RngElt] : Check := true, Normalize := false) -> SeqEnum
    {Returns the Hensel lift of the 4-theta null point tt to the
    precision of T2.}
    R := Universe(T2); assert IsInvertible(R!2);
    // Fix the normalization!
    A00, A02, A20, A22 := Explode(ProjectiveNormalization(T2));
    a00, a02, a20, a22, a01, a21, a10, a12, a11, a13 :=
	Explode(ProjectiveNormalization(tt));
    ////////////////////////////////////////////////////////////////////
    // Set up normilised squares...
    ////////////////////////////////////////////////////////////////////
    Lam := A00^2+A02^2+A20^2+A22^2;
    if Valuation(Lam) eq 0 then
	Lam_inv := Lam^-1;
	C00 := 1;
	C01 := 2*(A00*A02+A20*A22)*Lam_inv;
    else
	Lam := 2*(A00*A02+A20*A22);
	Lam_inv := Lam^-1;
	C00 := (A00^2+A02^2+A20^2+A22^2)*Lam_inv;
	C01 := 1;
    end if;
    C10 := 2*(A00*A20+A02*A22)*Lam_inv;
    C11 := 2*(A00*A22+A02*A20)*Lam_inv;
    ////////////////////////////////////////////////////////////////////
    // Solve for normalised square roots...
    ////////////////////////////////////////////////////////////////////
    lam_inv := Parent(a00)!Lam_inv;
    r01 := 2*(a01^2 + a21^2) * lam_inv; 
    r10 := 2*(a10^2 + a12^2) * lam_inv; 
    r11 := 2*(a11^2 + a13^2) * lam_inv; 
    ////////////////////////////////////////////////////////////////////
    // Use the relations:
    // 2(a00a02 + a20a22)/(a00^2+a02^2+a20^2+a22^2)
    //      = 4((a01^2+a21^2)/(a00^2+a02^2+a20^2+a22^2))^2,
    // etc.
    ////////////////////////////////////////////////////////////////////
    if C00 eq 1 then
	R00 := 1;
	R01 := HenselSqrt(C01,r01);
    else
	r00 := (a00^2+a02^2+a20^2+a22^2)*lam_inv;
	R00 := HenselSqrt(C00,r00);
	R01 := 1;
    end if;
    R10 := HenselSqrt(C10,r10);
    R11 := HenselSqrt(C11,r11);
    ////////////////////////////////////////////////////////////////////
    // Set up renormalised squares...
    ////////////////////////////////////////////////////////////////////
    S12 := Lam * R00 * R01; S34 := Lam * R10 * R11;
    S13 := Lam * R00 * R10; S24 := Lam * R01 * R11;
    S14 := Lam * R00 * R11; S23 := Lam * R01 * R10;
    //
    U12 := (S12 + S34)/2; V12 := (S12 - S34)/2;
    U13 := (S13 + S24)/2; V13 := (S13 - S24)/2;
    U14 := (S14 + S23)/2; V14 := (S14 - S23)/2;
    ////////////////////////////////////////////////////////////////////
    // Solve for normalised square roots...
    ////////////////////////////////////////////////////////////////////
    y12 := a01 + a21; z12 := a01 - a21;
    y13 := a10 + a12; z13 := a10 - a12;
    y14 := a11 + a13; z14 := a11 - a13; 
    ////////////////////////////////////////////////////////////////////
    // Use the relations:
    // (a01 + a21)^2 = s14 + s23
    // 
    // etc.
    ////////////////////////////////////////////////////////////////////
    Y12 := HenselSqrt(U12,y12); Z12 := HenselSqrt(V12,z12);
    Y13 := HenselSqrt(U13,y13); Z13 := HenselSqrt(V13,z13);
    Y14 := HenselSqrt(U14,y14); Z14 := HenselSqrt(V14,z14);
    ////////////////////////////////////////////////////////////////////
    A01 := (Y12 + Z12)/2; A21 := (Y12 - Z12)/2;
    A10 := (Y13 + Z13)/2; A12 := (Y13 - Z13)/2;
    A11 := (Y14 + Z14)/2; A13 := (Y14 - Z14)/2;
    ////////////////////////////////////////////////////////////////////
    TT := [ A00, A02, A20, A22, A01, A21, A10, A12, A11, A13 ];
    if Check then
	assert IsValidLevel4ThetaNullPoint(TT);
    end if;
    if Normalize then
	TT := ProjectiveNormalization(TT);
    end if;
    return TT;
end intrinsic;

intrinsic ExistsLevel4ThetaNullPointFromIsogenousLevel2ThetaNullPoint(
    tt::SeqEnum[RngElt] : Check := true, Normalize := false) -> SeqEnum
    {A theta null point is computed that has 2-torsion part equal to the given point.}
    K := Universe(tt);      
    require Characteristic(K) ne 2 :
        "Universe of argument must not have characteristic 2."; 
    require #tt eq 4 : 
        "Argument must consist of four theta constants."; 
    a00, a02, a20, a22 := Explode(Eltseq(tt));
    ////////////////////////////////////////////////////////////////////
    // Set up normilised squares...
    ////////////////////////////////////////////////////////////////////
    lam := (a00^2+a02^2+a20^2+a22^2);
    lam_inv := lam^-1;
    C00 := 1;
    C01 := 2*(a00*a02+a20*a22)*lam_inv;
    C10 := 2*(a00*a20+a02*a22)*lam_inv;
    C11 := 2*(a00*a22+a02*a20)*lam_inv;
    ////////////////////////////////////////////////////////////////////
    // Solve for normalised square roots...
    ////////////////////////////////////////////////////////////////////
    R00 := 1; 
    bool, R01 := IsSquare(C01);
    if not bool then return false, _; end if;
    bool, R10 := IsSquare(C10);
    if not bool then return false, _; end if;
    bool, R11 := IsSquare(C11);
    if not bool then return false, _; end if;
    // print "[r00,r01,r10,r11] =", [R00,R01,R10,R11];
    ////////////////////////////////////////////////////////////////////
    // Set up renormalised squares...
    ////////////////////////////////////////////////////////////////////
    S12 := lam * R00 * R01; S34 := lam * R10 * R11;
    S13 := lam * R00 * R10; S24 := lam * R01 * R11;
    S14 := lam * R00 * R11; S23 := lam * R01 * R10;
    //
    U12 := (S12 + S34)/2; V12 := (S12 - S34)/2;
    U13 := (S13 + S24)/2; V13 := (S13 - S24)/2;
    U14 := (S14 + S23)/2; V14 := (S14 - S23)/2;
    // print "[u12,u13,u14] =", [U12,U13,U14];
    // print "[v12,v13,v14] =", [V12,V13,V14];
    ////////////////////////////////////////////////////////////////////
    // Solve for normalised square roots...
    ////////////////////////////////////////////////////////////////////
    bool1, Y12 := IsSquare(U12); bool2, Z12 := IsSquare(V12);
    if not (bool1 and bool2) then return false, _; end if;
    bool1, Y13 := IsSquare(U13); bool2, Z13 := IsSquare(V13);
    if not (bool1 and bool2) then return false, _; end if;
    bool1, Y14 := IsSquare(U14); bool2, Z14 := IsSquare(V14);
    if not (bool1 and bool2) then return false, _; end if;
    a01 := (Y12 + Z12)/2; a21 := (Y12 - Z12)/2;
    a10 := (Y13 + Z13)/2; a12 := (Y13 - Z13)/2;
    a11 := (Y14 + Z14)/2; a13 := (Y14 - Z14)/2;
    tt := [ a00, a02, a20, a22, a01, a21, a10, a12, a11, a13 ];
    if Check then
	assert IsValidLevel4ThetaNullPoint(tt);
    end if;
    if Normalize then
        tt := ProjectiveNormalization(tt);
    end if;
    return true, tt;
end intrinsic;

intrinsic Level4ThetaNullPointFromIsogenousLevel2ThetaNullPoint(
    tt::SeqEnum[RngElt] : Check := true) -> SeqEnum
    {}
    FF := Universe(tt); 
    require Characteristic(FF) ne 2:
        "Argument must be defined over a finite field of odd characteristic.";
    require #tt eq 4 :
        "Argument must be a sequence of four theta constants.";
    bool, tt4 := ExistsLevel4ThetaNullPointFromIsogenousLevel2ThetaNullPoint(tt : Check := Check);
    require bool : "Argument must admit a 4-theta structure.";
    return tt4;
end intrinsic;

intrinsic Level4ThetaNullPointFromIsogenousLevel2ThetaNullPointOverSplittingField(
    tt::SeqEnum[FldElt] : Check := true, Normalize := false) -> SeqEnum
    {A theta null point is computed that has 2-torsion part equal to the given
    point. Note that this depends on some choices. Possibly one has to extend
    the base field.}
    K := Universe(tt);      
    require Characteristic(K) ne 2 :
        "Universe of argument must not have characteristic 2."; 
    a00, a02, a20, a22 := Explode(Eltseq(tt));
    ////////////////////////////////////////////////////////////////////
    // Set up normilised squares...
    ////////////////////////////////////////////////////////////////////
    lam := (a00^2+a02^2+a20^2+a22^2); lam_inv := lam^-1;
    C00 := 1;
    C01 := 2*(a00*a02+a20*a22)*lam_inv;
    C10 := 2*(a00*a20+a02*a22)*lam_inv;
    C11 := 2*(a00*a22+a02*a20)*lam_inv;
    ////////////////////////////////////////////////////////////////////
    // Solve for normalised square roots...
    ////////////////////////////////////////////////////////////////////
    K := SplittingField({ X^2-C01, X^2-C10, X^2-C11 })
	where X := PolynomialRing(K).1;
    R00 := 1;
    R01 := Sqrt(K!C01);
    R10 := Sqrt(K!C10);
    R11 := Sqrt(K!C11);
    ////////////////////////////////////////////////////////////////////
    // Set up renormalised squares...
    ////////////////////////////////////////////////////////////////////
    S12 := lam * R00 * R01; S34 := lam * R10 * R11;
    S13 := lam * R00 * R10; S24 := lam * R01 * R11;
    S14 := lam * R00 * R11; S23 := lam * R01 * R10;
    //
    U12 := (S12 + S34)/2; V12 := (S12 - S34)/2;
    U13 := (S13 + S24)/2; V13 := (S13 - S24)/2;
    U14 := (S14 + S23)/2; V14 := (S14 - S23)/2;
    ////////////////////////////////////////////////////////////////////
    // Solve for normalised square roots...
    ////////////////////////////////////////////////////////////////////
    K := SplittingField({
	X^2-U12, X^2-V12, X^2-U13, X^2-V13, X^2-U14, X^2-V14 })
	where X := PolynomialRing(K).1;
    Y12 := Sqrt(K!U12); Z12 := Sqrt(K!V12);
    Y13 := Sqrt(K!U13); Z13 := Sqrt(K!V13);
    Y14 := Sqrt(K!U14); Z14 := Sqrt(K!V14);
    a01 := (Y12+Z12)/2; a21 := (Y12-Z12)/2;
    a10 := (Y13+Z13)/2; a12 := (Y13-Z13)/2;
    a11 := (Y14+Z14)/2; a13 := (Y14-Z14)/2;
    tt := [ a00, a02, a20, a22, a01, a21, a10, a12, a11, a13 ];
    if Check then
	assert IsValidLevel4ThetaNullPoint(tt);
    end if;
    if Normalize then
        tt := ProjectiveNormalization(tt);
    end if;
    return tt;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Maps from theta moduli space (Theta constants) to Rosenhain 
//////////////////////////////////////////////////////////////////////////////

/*
intrinsic Level2ThetaNullPointToRosenhainGaudry(tt::SeqEnum) -> SeqEnum
    {Given theta constants [a00,a02,a20,a22] for the 2-torsion part of
    the 4-theta null point of the Jacobian of a curve C, solves for an
    associated set of Rosenhain invariants.}
    ss := [ ti^2 : ti in Eltseq(tt) ];
    s1, s2, s3, s4 := Explode(ss);
    // s8 and s10 in Gaudry's theta functions arithmetic article
    s5_plus_s6 := Sqrt((s1+s2)^2-(s3+s4)^2);
    s5_minu_s6 := Sqrt((s1-s2)^2-(s3-s4)^2);
    s5 := (s5_plus_s6 + s5_minu_s6)/2;
    s6 := (s5_plus_s6 - s5_minu_s6)/2;
    e1 := (s1*s3)/(s2*s4);
    e2 := (s3*s5)/(s4*s6);
    e3 := (s1*s5)/(s2*s6);
    return [ e1, e2, e3 ];
end intrinsic;
*/

intrinsic IsogenousLevel2ThetaNullPointToRosenhainInvariants(tt::SeqEnum : All := true) -> SeqEnum
    {Given theta constants [a00,a02,a20,a22] for the 2-torsion part of
    the 4-theta null point of the Jacobian of a curve C, solves for an
    associated set of Rosenhain invariants.}
    print "Warning: This is not a morphism, and not consistent with other maps used."; 
    require #tt eq 4 : "Argument must consist of four 4-theta constants.";
    bool := IsInvertible(Universe(tt)!2);
    require bool : "Universe of argument must contain an inverse of 2.";
    a00, a02, a20, a22 := Explode(tt);
    e1 := ((a00*a02)/(a22*a20))^2;
    A := ((a02*a22)^2 - (a00*a20)^2)*a02^4;
    B := (a00^4 - a02^4 + a20^4 - a22^4)*(a20*a22)^2;
    C := ((a02*a22)^2 - (a00*a20)^2)*a22^4;
    bool, D := IsSquare(B^2-4*A*C);
    require bool : "Argument does not determine Rosenhain invariants.";
    e2 := (D-B)/(2*A); 
    e3 := e2*((a00*a22)/(a02*a20))^2;
    if All then
	f2 := e2 - D/A;
	f3 := f2*((a00*a22)/(a02*a20))^2;
	return [ e1, e2, e3 ], [ e1, f2, f3 ];
    end if;
    return [ e1, e2, e3 ];
end intrinsic;
    
/////////////////////////////////////////////////////////////////////////////
// Mappings from Rosenhain moduli to absolute Igusa invariants.            //
/////////////////////////////////////////////////////////////////////////////

intrinsic RosenhainToAbsoluteIgusaInvariants(tt::[RngElt]) -> SeqEnum
    {The absolute (Igusa) invariants of the hyperelliptic curve
    y^2 = x(x-1)(x-t0)(x-t1)(x-t2) where tt = [t0,t1,t2].}
    require #tt eq 3 : "Argument must be a sequence of three elements.";
    t0, t1, t2 := Explode(tt);
    x := PolynomialRing(Universe(tt)).1;
    FF := Universe(tt);
    if IsField(FF) and IsExact(FF) then
        C := HyperellipticCurve(x*(x-1)*(x-t0)*(x-t1)*(x-t2));
        return AbsoluteIgusaInvariants(C);
    end if;
    f := x*(x-1)*(x-t0)*(x-t1)*(x-t2);
    JJ := IgusaInvariants(f);
    J2, J4, J6, J8, J10 := Explode(JJ);
    bool, UU := IsInvertible(J10);
    require bool : "Isogenous Igusa invariants are degenerate.";
    return [ J2^5*UU, J2^3*J4*UU, J2^2*J6*UU, J2*J8*UU, J4*J6*UU,
        J4*J8^2*UU^2, J6^2*J8*UU^2, J6^5*UU^3, J6*J8^3*UU^3, J8^5*UU^4 ];
end intrinsic;

intrinsic RosenhainToRichelotIgusaInvariants(
    tt::[RngElt] : Normalized := false) -> SetEnum
    {The Igusa invariants of the Richelot codomain hyperelliptic
    curve of y^2 = x(x-1)(x-t0)(x-t1)(x-t2) where tt = [t0,t1,t2].}
    HH := ModularRichelotPolynomials(tt);
    FF := Universe(tt);
    if not (IsField(FF) and IsExact(FF)) then
	/* For p-adic rings, the leading coefficient (of degree 3) can
        fail to fully cancel, so we manually chop it off here. */
	for i in [1..3] do
	    if Degree(HH[i]) eq 3 then
		HH[i] := Polynomial(Coefficients(HH[i])[[1..3]]);
	    end if;
	end for;
    end if;
    JJ := IgusaInvariants(&*HH);
    if Normalized then
	JJ := IgusaToNormalizedIgusaInvariants(JJ);
    end if;
    return JJ;
end intrinsic;

intrinsic RosenhainToRichelotAbsoluteIgusaInvariants(tt::[RngElt]) -> SetEnum
    {The absolute Igusa invariants of the Richelot codomain hyperelliptic
    curve of y^2 = x(x-1)(x-t0)(x-t1)(x-t2) where tt = [t0,t1,t2].}
    JJ := RosenhainToRichelotIgusaInvariants(tt);
    J2, J4, J6, J8, J10 := Explode(JJ);
    bool, UU := IsInvertible(J10);
    require bool : "Isogenous Igusa invariants are degenerate.";
    return [
	J2^5*UU, J2^3*J4*UU, J2^2*J6*UU, J2*J8*UU, J4*J6*UU,
        J4*J8^2*UU^2, J6^2*J8*UU^2, J6^5*UU^3, J6*J8^3*UU^3, J8^5*UU^4 ];
end intrinsic;

/////////////////////////////////////////////////////////////////////////////
// Mappings between Satake invariants (power sums) and Igusa invariants
/////////////////////////////////////////////////////////////////////////////

intrinsic SatakeToIgusaClebschInvariants(ss::SeqEnum[RngElt]) -> SeqEnum
    {Satake invariants [s2,s3,s5,s6] to Igusa-Clebsch invariants.}
    R := Universe(ss);
    //require IsUnit(R!30) : "Primes 2, 3, and 5 must be units in universe of argument.";
    s2,s3,s5,s6 := Explode(ss);
    require 5*s3*s2 ne 12*s5 : 
        "Arugment lies on H1 thus does not correspond to a Jacobian of a genus 2 curve.";
    psi4 := s2/12;
    psi6 := s3/12;
    chi10 := (60*psi4*psi6 - s5)/(2^14*3^5*5);
    chi12 := (s6 - 108*psi4^3 - 24*psi6^2)/(2^15*3^7);
    I2 := -2^3*3*chi12/chi10;
    I4 := 2^2*psi4;
    I6 := -(2^3*psi6 - I2*I4)/3;
    I10 := -2^14*chi10;
    return [I2,I4,I6,I10];
end intrinsic;

intrinsic IgusaClebschToSatakeInvariants(II::SeqEnum[RngElt]) -> SeqEnum
    {Igusa-Clebsch invariants [I2,I4,I6,I10] to Satake invariants.}
    R := Universe(II);
    require IsUnit(R!30) : "Primes 2, 3, and 5 must be units in universe of argument.";
    I2,I4,I6,I10 := Explode(II);
    s2 := 3*I4;
    s3 := 3*(I2*I4 - 3*I6)/2;
    s5 := 3*5*(I2*I4^2 - 3*I4*I6 + 648*I10)/8;
    s6 := 3*(2*I2^2*I4^2 - 12*I2*I4*I6 + 972*I2*I10 + 9*I4^3 + 18*I6^2)/16;
    return [s2,s3,s5,s6];
end intrinsic;

intrinsic SatakeToIgusaInvariants(ss::SeqEnum[RngElt]) -> SeqEnum
    {Satake invariants [s2,s3,s5,s6] to Igusa invariants.}
    R := Universe(ss);
    //require IsUnit(R!30) : "Primes 2, 3, and 5 must be units in universe of argument.";
    s2,s3,s5,s6 := Explode(ss);
    require 5*s3*s2 ne 12*s5 : 
        "Argument lies on H1, thus does not correspond to a Jacobian of a genus 2 curve.";
    II := SatakeToIgusaClebschInvariants(ss);
    return IgusaClebschToIgusaInvariants(II);
end intrinsic;

intrinsic IgusaToSatakeInvariants(JJ::SeqEnum[RngElt]) -> SeqEnum
    {Igusa invariants [s2,s3,s5,s6] to Satake invariants.}
    R := Universe(JJ);
    require IsUnit(R!30) : "Primes 2, 3, and 5 must be units in universe of argument.";
    J2,J4,J6,_,J10 := Explode(JJ);
    s2 := 12*(J2^2 - 24*J4);
    s3 := 12*(J2^3 - 36*J2*J4 + 216*J6);
    s5 := 60*(J2^5 - 60*J2^3*J4 + 216*J2^2*J6 + 864*J2*J4^2 - 5184*J4*J6 + 82944*J10);
    s6 := 12*(11*J2^6 - 792*J2^4*J4 + 864*J2^3*J6 + 18144*J2^2*J4^2 - 31104*J2*J4*J6 + 497664*J2*J10 - 124416*J4^3 + 93312*J6^2);
    return [s2,s3,s5,s6];
end intrinsic;

intrinsic IgusaClebschToAbsoluteStrengInvariants(II::SeqEnum[RngElt]) -> SeqEnum
    {}
    require #II eq 4 : "Argument must be a sequence of length 4.";
    I2, I4, I6, I10 := Explode(II);
    bool, U10 := IsInvertible(I10);
    require bool : "Element 4 of argument must be invertible";
    I6p := (I2*I4 - 3*I6)/2;
    /*
    i1 := 2^8*I4*I6p*U10;
    i2 := 2^5*I2*I4^2*U10;
    i3 := 2^14*I4^5*U10^2;
    */
    j1 := I4*I6p*U10;
    j2 := I2*I4^2*U10;
    j3 := I4^5*U10^2;
    return [j1,j2,j3];
end intrinsic;

/*
intrinsic IgusaToAbsoluteStrengInvariants(JJ::SeqEnum[RngElt]) -> SeqEnum
    {}
    require #JJ eq 5 : "Argument must be a sequence of length 5.";
    J2, J4, J6, J8, J10 := Explode(JJ);
    bool, U10 := IsInvertible(J10);
    require bool : "Element 5 of argument must be invertible";
    i1 := (J2^2 - 24*J4)*(J2^3 - 36*J2*J4 + 216*J6) * U10;
    i2 := J2 * (J2^2 - 24*J4)^2 * U10;
    i3 := (J2^2 - 24*J4)^5 * U10^2;
    return [i1,i2,i3];
end intrinsic;
*/

intrinsic IgusaToAbsoluteStrengInvariants(JJ::SeqEnum[RngElt]) -> SeqEnum
    {}
    require #JJ eq 5 : "Argument must be a sequence of 5 Igusa invariants.";
    // The inverse transformation:
    J2, J4, J6, J8, J10 := Explode(JJ);
    require 4*J8 eq (J2*J6 - J4^2) : "Argument must be a sequence of 5 Igusa invariants.";
    bool, U10 := IsInvertible(J10);
    require bool : "Element 5 of argument must be invertible";
    return [
        (J2^2 - 24*J4)*(J2^3 - 36*J2*J4 + 216*J6)*U10/2^8, // j1
        J2*(J2^2 - 24*J4)^2*U10/2^5, // j2
        (J2^2 - 24*J4)^5*U10^2/2^14 // j3
    ];
end intrinsic;

intrinsic AbsoluteStrengToIgusaInvariants(jj::[RngElt]) -> SeqEnum
    {Given a triple jj = [j1,j2,j3] of Streng invariants 
    [I4*psi6/I10,I2*I4^2/I10,I4^5/I10^2] where psi6=(I2.I4 - 3.I6)/2),
    return the associated 5-tuple of Igusa invariants.}
    // Streng uses the triple of invariants jj = [j1,j2,j3] 
    // = [I4*psi6/I10,I2*I4^2/I10,I4^5/I10^2] where psi6=(I2I4-3I6)/2)
    require #jj eq 3 : "Argument 1 must be a sequence of 3 Streng invariants.";
    j1, j2, j3 := Explode(jj);
    return [
        1,
        (j2^2 - 16*j3)/(24*j2^2),
        (256*j1*j3 + j2^3 - 48*j2*j3)/(432*j2^3),
        (1024*j1*j2*j3 + j2^4 - 96*j2^2*j3 - 768*j3^2)/(6912*j2^4),
        8*j3^2/j2^5
        ];
end intrinsic;

