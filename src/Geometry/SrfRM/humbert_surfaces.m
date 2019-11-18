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

/* Humbert polynomial */

// Known Satake discriminants:
SatakeDiscriminants := [ 1, 4, 5, 8, 12, 13, 16, 17, 20, 21 ];
// Known Rosenhain discriminants:
RosenhainDiscriminants := [ 1, 4, 5, 8, 12, 13, 16, 17, 20 ];
// Known level 2 theta discriminants:
Level2ThetaDiscriminants := [ 1, 4, 5, 8, 12, 13, 16, 17, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 68 ];

//////////////////////////////////////////////////////////////////////////////
// Level 1 theta: Satake Humbert polynomials 
//////////////////////////////////////////////////////////////////////////////

// Field discriminant 01
// 01:
import "Level1Satake/humbert_01.m": SatakeHumbertPolynomial01;
// 04 = 01*02^2:
import "Level1Satake/humbert_04.m": SatakeHumbertPolynomial04;
// 09 = 01*03^2:
import "Level1Satake/humbert_09.m": SatakeHumbertPolynomial09;
// 16 = 01*04^2:
import "Level1Satake/humbert_16.m": SatakeHumbertPolynomial16;
// Field discriminant 05
// 05:
import "Level1Satake/humbert_05.m": SatakeHumbertPolynomial05;
// 20 = 05*02^2:
import "Level1Satake/humbert_20.m": SatakeHumbertPolynomial20;
// Field discriminant 08
// 08:
import "Level1Satake/humbert_08.m": SatakeHumbertPolynomial08;
// Field discriminant 12
// 12:
import "Level1Satake/humbert_12.m": SatakeHumbertPolynomial12;
// Field discriminant 13
// 13:
import "Level1Satake/humbert_13.m": SatakeHumbertPolynomial13;
// Field discriminant 17
// 17:
import "Level1Satake/humbert_17.m": SatakeHumbertPolynomial17;
// Field discriminant 21
// 21:
import "Level1Satake/humbert_21.m": SatakeHumbertPolynomial21;

//////////////////////////////////////////////////////////////////////////////
// Rosenhain: Level 2 Humbert polynomials
//////////////////////////////////////////////////////////////////////////////

// Field discriminant 01
// 01: Split Jacobians are degenerate:
import "Level2Rosenhain/humbert_01.m": RosenhainHumbertPolynomial01, RosenhainHumbertPolynomials01;
// 04 = 01*02^2:
import "Level2Rosenhain/humbert_04.m": RosenhainHumbertPolynomial04, RosenhainHumbertPolynomials04;
// 09 = 01*03^2:
import "Level2Rosenhain/humbert_09.m": RosenhainHumbertPolynomial09, RosenhainHumbertPolynomials09;
// 16 = 01*04^2:
import "Level2Rosenhain/humbert_16.m": RosenhainHumbertPolynomial16, RosenhainHumbertPolynomials16;
// Field discriminant 05
// 05:
import "Level2Rosenhain/humbert_05.m": RosenhainHumbertPolynomial05, RosenhainHumbertPolynomials05;
// 20 = 05*02^2:
import "Level2Rosenhain/humbert_20.m": RosenhainHumbertPolynomial20, RosenhainHumbertPolynomials20;
// Field discriminant 08
// 08:
import "Level2Rosenhain/humbert_08.m": RosenhainHumbertPolynomial08, RosenhainHumbertPolynomials08;
// Field discriminant 12
// 12:
import "Level2Rosenhain/humbert_12.m": RosenhainHumbertPolynomial12, RosenhainHumbertPolynomials12;
// Field discriminant 13
// 13:
import "Level2Rosenhain/humbert_13.m": RosenhainHumbertPolynomial13, RosenhainHumbertPolynomials13;
// Field discriminant 17
// 17:
import "Level2Rosenhain/humbert_17.m": RosenhainHumbertPolynomial17, RosenhainHumbertPolynomials17; 

//////////////////////////////////////////////////////////////////////////////
// Level 2 theta Humbert polynomials
//////////////////////////////////////////////////////////////////////////////

// Field discriminant 01
// 01:
import "Level2Theta/humbert_01.m": Level2ThetaNullHumbertPolynomials01;
// 04 = 01*02^2:
import "Level2Theta/humbert_04.m": Level2ThetaNullHumbertPolynomials04;
// 09 = 01*03^2:
import "Level2Theta/humbert_09.m": Level2ThetaNullHumbertPolynomials09;
// 16 = 01*04^2:
import "Level2Theta/humbert_16.m": Level2ThetaNullHumbertPolynomials16;
// 36 = 01*06^2:
import "Level2Theta/humbert_36.m": Level2ThetaNullHumbertPolynomials36;
// Field discriminant 05
// 05:
import "Level2Theta/humbert_05.m": Level2ThetaNullHumbertPolynomials05;
// 20 = 05*02^2:
import "Level2Theta/humbert_20.m": Level2ThetaNullHumbertPolynomials20;
// Field discriminant 08
// 08:
import "Level2Theta/humbert_08.m": Level2ThetaNullHumbertPolynomials08;
// 32 = 08*2^2:
import "Level2Theta/humbert_32.m": Level2ThetaNullHumbertPolynomials32;
// Field discriminant 12
// 12:
import "Level2Theta/humbert_12.m": Level2ThetaNullHumbertPolynomials12;
// 48 = 12*02^2:
import "Level2Theta/humbert_48.m": Level2ThetaNullHumbertPolynomials48;
// Field discriminant 13
// 13:
import "Level2Theta/humbert_13.m": Level2ThetaNullHumbertPolynomials13;
// 52 = 13*02^2:
import "Level2Theta/humbert_52.m": Level2ThetaNullHumbertPolynomials52;
// Field discriminant 17
// 17:
import "Level2Theta/humbert_17.m": Level2ThetaNullHumbertPolynomials17;
// 68 = 17*02^2:
import "Level2Theta/humbert_68.m": Level2ThetaNullHumbertPolynomials68;
// Field discriminant 24
// 24:
import "Level2Theta/humbert_24.m": Level2ThetaNullHumbertPolynomials24;
// Field discriminant 28
// 28:
import "Level2Theta/humbert_28.m": Level2ThetaNullHumbertPolynomials28;
// Field discriminant 40
// 40:
import "Level2Theta/humbert_40.m": Level2ThetaNullHumbertPolynomials40;
// Field discriminant 44
// 44:
import "Level2Theta/humbert_44.m": Level2ThetaNullHumbertPolynomials44;
// Field discriminant 56
// 56:
import "Level2Theta/humbert_56.m": Level2ThetaNullHumbertPolynomials56;
// Field discriminant 60
// 60:
import "Level2Theta/humbert_60.m": Level2ThetaNullHumbertPolynomials60;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic RosenhainHumbertPolynomialPullback(
    R::Rng,D::RngIntElt,i::RngIntElt) -> RngMPolElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    hD_components := RosenhainHumbertPolynomials(R,D);
    r := #hD_components;
    require i ge 1 and i le r : "Argument 3 must be a positive integer at most", r;
    FF<a00,a02,a20,a22> := FunctionField(R, 4 : Global);
    tt := [a00,a02,a20,a22];
    ee := Level2ThetaNullPointToRosenhainInvariants(tt);
    fD := Numerator(Evaluate(hD_components[i],ee));
    if D in {1,4} then return fD; end if;
    f01_comps := Level2ThetaNullHumbertPolynomials(R,1);
    for f01 in f01_comps do
	repeat
	    gcd := GCD(fD,f01);
	    if gcd ne 1 then
		fD div:= gcd;
		//print "gcd =", gcd;
	    end if;
	until gcd eq 1;
    end for;
    return fD;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Projective Rosenhain Humbert polynomials
//////////////////////////////////////////////////////////////////////////////

intrinsic ProjectiveRosenhainHumbertPolynomial(R::Rng,D::RngIntElt) -> RngMPolElt
    {}
    return ProjectiveRosenhainHumbertPolynomial(R,D,1);
end intrinsic;
    
intrinsic ProjectiveRosenhainHumbertPolynomial(R::Rng,D::RngIntElt,i::RngIntElt) -> RngMPolElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    hD := RosenhainHumbertPolynomial(R,D,i);
    P3 := Parent(hD);
    P4<e0,e1,e2,e3> := PolynomialRing(R,4 : Global);
    if D ne 1 then
        return Homogenization(Evaluate(hD,[e1,e2,e3]),e0);
    else
        return Homogenization(Evaluate(hD,[e1,e2,e3]),e0,1);
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Level 1 Satake Humbert polynomials
//////////////////////////////////////////////////////////////////////////////

intrinsic Level1SatakeHumbertPolynomial(R::Rng,D::RngIntElt) -> SetIndx
    {The defining polynomial for the Humbert surface of discriminant D 
    in the space of symmetric Satake invariants (s2:s3:s5:s6).}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    case D:
    when 01:
	return SatakeHumbertPolynomial01(R);
    when 04:
	return SatakeHumbertPolynomial04(R);
    when 05:
	return SatakeHumbertPolynomial05(R);
    when 08:
	return SatakeHumbertPolynomial08(R);
    when 09:
	return SatakeHumbertPolynomial09(R);
    when 12:
	return SatakeHumbertPolynomial12(R);
    when 13:
	return SatakeHumbertPolynomial13(R);
    when 16:
	return SatakeHumbertPolynomial16(R);
    when 17:
	return SatakeHumbertPolynomial17(R);
    when 20:
	return SatakeHumbertPolynomial20(R);
    when 21:
	return SatakeHumbertPolynomial21(R);
    end case;
    require false:
	"Satake Humbert polynomial not computed for discriminant D =", D;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Level 2 Rosenhain Humbert polynomials
//////////////////////////////////////////////////////////////////////////////

intrinsic RosenhainHumbertPolynomial(R::Rng,D::RngIntElt) -> SetIndx
    {The defining polynomials for the components of the Humbert surface
    of discriminant D in the space of Rosenhain invariants.}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    case D:
    when 01:
	return RosenhainHumbertPolynomial01(R);
    when 04:
	return RosenhainHumbertPolynomial04(R);
    when 05:
	return RosenhainHumbertPolynomial05(R);
    when 08:
	return RosenhainHumbertPolynomial08(R);
    when 09:
	return RosenhainHumbertPolynomial09(R);
    when 12:
	return RosenhainHumbertPolynomial12(R);
    when 13:
	return RosenhainHumbertPolynomial13(R);
    when 16:
	return RosenhainHumbertPolynomial16(R);
    when 17:
	return RosenhainHumbertPolynomial17(R); 
    when 20:
	return RosenhainHumbertPolynomial20(R);
    end case;
    require false:
	"Rosenhain Humbert polynomial not computed for discriminant D =", D;
end intrinsic;

intrinsic RosenhainHumbertPolynomials(R::Rng,D::RngIntElt) -> SetIndx
    {The defining polynomials for the components of the Humbert surface
    of discriminant D in the space of Rosenhain invariants.}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    case D:
    when 01:
	return RosenhainHumbertPolynomials01(R);
    when 04:
	return RosenhainHumbertPolynomials04(R);
    when 05:
	return RosenhainHumbertPolynomials05(R);
    when 08:
	return RosenhainHumbertPolynomials08(R);
    when 09:
	return RosenhainHumbertPolynomials09(R);
    when 12:
	return RosenhainHumbertPolynomials12(R);
    when 13:
	return RosenhainHumbertPolynomials13(R);
    when 16:
	return RosenhainHumbertPolynomials16(R);
    when 17:
	return RosenhainHumbertPolynomials17(R); 
    when 20:
	return RosenhainHumbertPolynomials20(R);
    end case;
    require false:
	"Rosenhain Humbert polynomial not computed for discriminant D =", D;
end intrinsic;

intrinsic RosenhainHumbertPolynomial(R::Rng,D::RngIntElt,i::RngIntElt) -> RngMPolElt
    {The defining polynomial for the i-th component of the Humbert surface 
    of discriminant D in the space of Rosenhain invariants.}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    hD_components := RosenhainHumbertPolynomials(R,D); r := #hD_components;
    require i ge 1 and i le r : "Argument 3 must be a positive integer at most", r;
    return hD_components[i];
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Level 2 theta Humbert polynomials (after Runge)
//////////////////////////////////////////////////////////////////////////////

intrinsic Level2ThetaNullHumbertPolynomial(R::Rng,D::RngIntElt) -> RngMPolElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    return Level2ThetaNullHumbertPolynomial(R,D,1);
end intrinsic;
    
intrinsic Level2ThetaNullHumbertPolynomial(R::Rng,D::RngIntElt,i::RngIntElt) -> RngMPolElt
    {The defining polynomial for the i-th component of the Humbert surface
    of discriminant D in the level 2 theta null space (a00:a02:a20:a22).}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    fD_components := Level2ThetaNullHumbertPolynomials(R,D); r := #fD_components;
    require i ge 1 and i le r : "Argument 3 must be a positive integer at most", r;
    return fD_components[i];
end intrinsic;

intrinsic Level2ThetaNullHumbertPolynomials(R::Rng,D::RngIntElt) -> SeqEnum
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument 2 must be a positive discriminant.";
    case D:
    when 01:
	return Level2ThetaNullHumbertPolynomials01(R);
    when 04:
	return Level2ThetaNullHumbertPolynomials04(R);
    when 05:
	return Level2ThetaNullHumbertPolynomials05(R);
    when 08:
	return Level2ThetaNullHumbertPolynomials08(R);
    when 09:
	return Level2ThetaNullHumbertPolynomials09(R);
    when 12:
	return Level2ThetaNullHumbertPolynomials12(R);
    when 13:
	return Level2ThetaNullHumbertPolynomials13(R);
    when 16:
	return Level2ThetaNullHumbertPolynomials16(R);
    when 17:
	return Level2ThetaNullHumbertPolynomials17(R);
    when 20:
	return Level2ThetaNullHumbertPolynomials20(R);
    when 24:
	return Level2ThetaNullHumbertPolynomials24(R);
    when 28:
	return Level2ThetaNullHumbertPolynomials28(R);
    when 32:
	return Level2ThetaNullHumbertPolynomials32(R);
    when 36:
	return Level2ThetaNullHumbertPolynomials36(R);
    when 40:
	return Level2ThetaNullHumbertPolynomials40(R);
    when 44:
	return Level2ThetaNullHumbertPolynomials44(R);
    when 48:
	return Level2ThetaNullHumbertPolynomials48(R);
    when 52:
	return Level2ThetaNullHumbertPolynomials52(R);
    when 56:
	return Level2ThetaNullHumbertPolynomials56(R);
    when 60:
	return Level2ThetaNullHumbertPolynomials60(R);
    when 68:
	return Level2ThetaNullHumbertPolynomials68(R);
    end case;
    require false:
	"Level 2 theta null Humbert surface not computed for discriminant D =", D;
end intrinsic;


