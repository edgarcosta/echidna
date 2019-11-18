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

intrinsic RandomAffineLevel2ThetaNullPointWithRM(FF::FldFin,D::RngIntElt :
    AbsolutelySimple := true) -> SeqEnum
    {N.B. The outputs lies on one particular choice of component.}
    if Characteristic(FF) eq 2 then
        /*
        Let x = (x1,x2,x3) be a affine level 2 theta null point, and s = (s1,s2,s3)
        be the symmetric invariants of x.  The Igusa invariants of this curve are:

        JJ = ( 1 : 
               (s2^2/s3)^2 : 
               (s2^2/s3)^4 :
               ((s1^2*s3^4 + s2^8 + s2^6*s3)/s3^4)^2 : s3^2 ).

        Conversely the point s can be recovered from JJ over a finite field. 
        */
        case D:
        when 5:
            // H := x1^4 + x2^4 + x3^4 + x1*x2*x3;
            repeat
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H := x1^4 + x2^4 + x3^4 + x1*x2*x3;
                bool, x1 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 8:
            // H := x1^2 + x2^2 + x3;
            repeat
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := x1^2 + x2^2;
            until x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 12:
            // H := x1^4 + x1*x2 + x2^4 + x3^2;
            repeat
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := Sqrt(x1^4 + x1*x2 + x2^4);
            until x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 13:
            repeat
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := PolynomialRing(FF).1;
                H := x1^20 + x1^17*x2*x3 + x1^16*x2^4 + x1^16*x3^4 + x1^13*x2*x3
                    +  x1^10*x2^2*x3^2 + x1^9*x2^5*x3 + x1^9*x2*x3^5
                    + x1^8*x2^4*x3^4 + x1^8*x2^4 + x1^8*x3^4 + x1^7*x2^3*x3^3
                    + x1^5*x2^9*x3 + x1^5*x2^5*x3^5 + x1^5*x2^5*x3
                    + x1^5*x2*x3^9 + x1^5*x2*x3^5 + x1^4*x2^16 + x1^4*x2^8*x3^4
                    + x1^4*x2^8 + x1^4*x2^4*x3^8 + x1^4*x3^16 + x1^4*x3^8
                    + x1^3*x2^7*x3^3 + x1^3*x2^3*x3^7 + x1^3*x2^3*x3^3
                    + x1^2*x2^10*x3^2 + x1^2*x2^2*x3^10 + x1*x2^17*x3
                    + x1*x2^13*x3 + x1*x2^9*x3^5 + x1*x2^5*x3^9 + x1*x2^5*x3^5
                    + x1*x2*x3^17 + x1*x2*x3^13 + x2^20 + x2^16*x3^4 + x2^8*x3^4
                    + x2^4*x3^16 + x2^4*x3^8 + x3^20;
                bool, x3 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 17:
            repeat
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H := x1^8 + x1^5*x2^7*x3 + x1^5*x2^3*x3 + x1^4*x2^16 + x1^4*x2^12*x3^4
                    + x1^4*x2^8 + x1^4*x2^4*x3^4 + x1^3*x2^13*x3^3 + x1^3*x2^9*x3^3
                    + x1^3*x2^5*x3^3 + x1^3*x2*x3^3 + x1^2*x2^10*x3^2 + x1*x2^19*x3
                    + x1*x2^15*x3 + x1*x2^7*x3^5 + x1*x2^3*x3^5 + x2^24 + x2^16*x3^4
                    + x2^8*x3^4 + x3^8;
                bool, x1 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 24:
            repeat
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H := x1^6 + x1^4*x2^4 + x1^4*x3^4 + x1^3*x2^2 + x1^3*x3^2 + x1^2*x2^8
                    + x1^2*x3^8 + x1*x2^6 + x1*x2^4*x3^2 + x1*x2^2*x3^4 + x1*x3^6
                    + x2^12 + x2^8*x3^4 + x2^4*x3^8 + x2^2*x3^2 + x3^12;
                bool, x1 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 28:
            repeat
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H :=  x1^16 + x1^9*x2 + x1^4*x2^4 + x1^4*x3^2 + x1^3*x2^3
                    + x1*x2^9 + x1*x2*x3^4 + x2^16 + x2^4*x3^2 + x3^8;
                bool, x1 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 40:
            repeat
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H := x1^14 + x1^12*x2^4 + x1^12*x3^4 + x1^10*x2^8 + x1^10*x3^8 + x1^9*x2^2
                    + x1^9*x3^2 + x1^8*x2^12 + x1^8*x2^8*x3^4 + x1^8*x2^4*x3^8 + x1^8*x2^4
                    + x1^8*x3^12 + x1^8*x3^4 + x1^6*x2^16 + x1^6*x2^8 + x1^6*x3^16 + x1^6*x3^8
                    + x1^4*x2^20 + x1^4*x2^16*x3^4 + x1^4*x2^12 + x1^4*x2^8*x3^4 + x1^4*x2^4*x3^16 
                    + x1^4*x2^4*x3^8 + x1^4*x2^2*x3^2 + x1^4*x3^20 + x1^4*x3^12 + x1^3*x2^6
                    + x1^3*x3^6 + x1^2*x2^24 + x1^2*x2^16*x3^8 + x1^2*x2^16 + x1^2*x2^8*x3^16
                    + x1^2*x2^4*x3^4 + x1^2*x3^24 + x1^2*x3^16 + x1*x2^18 + x1*x2^16*x3^2
                    + x1*x2^8*x3^2 + x1*x2^6*x3^4 + x1*x2^4*x3^6 + x1*x2^2*x3^16 + x1*x2^2*x3^8
                    + x1*x3^18 + x2^28 + x2^24*x3^4 + x2^20*x3^8 + x2^16*x3^12 + x2^12*x3^16
                    + x2^10*x3^2 + x2^8*x3^20 + x2^8*x3^4 + x2^4*x3^24 + x2^4*x3^8 + x2^2*x3^10 + x3^28;
                bool, x1 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 44:
            repeat
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := PolynomialRing(FF).1;
                H := x1^28 + x1^25*x2 + x1^24*x2^4 + x1^24*x3^2 + x1^22*x2^2 + x1^20*x2^8
                    + x1^20*x3^4 + x1^19*x2^3 + x1^18*x2^6 + x1^18*x2^2*x3^2 + x1^17*x2^9 + x1^17*x2*x3^4 
                    + x1^17*x2 + x1^16*x2^12 + x1^16*x2^8*x3^2 + x1^16*x2^4*x3^4 + x1^16*x2^4 + x1^16*x3^6 
                    + x1^14*x2^2 + x1^13*x2^5 + x1^12*x2^16 + x1^12*x2^8 + x1^12*x2^4*x3^2 + x1^12*x3^8 
                    + x1^11*x2^3 + x1^10*x2^2*x3^2 + x1^9*x2^17 + x1^9*x2*x3^8 + x1^8*x2^20 + x1^8*x2^16*x3^2
                    + x1^8*x2^12 + x1^8*x2^4*x3^8 + x1^8*x2^4*x3^4 + x1^8*x2^4 + x1^8*x3^10 + x1^8*x3^2 
                    + x1^7*x2^7 + x1^6*x2^18 + x1^6*x2^6*x3^2 + x1^6*x2^2*x3^8 + x1^6*x2^2*x3^4 + x1^5*x2^13 
                    + x1^5*x2^5*x3^4 + x1^5*x2*x3^2 + x1^4*x2^24 + x1^4*x2^16*x3^4 + x1^4*x2^16 
                    + x1^4*x2^12*x3^2 + x1^4*x2^8*x3^8 + x1^4*x2^8*x3^4 + x1^4*x2^8 + x1^4*x2^4*x3^6 
                    + x1^4*x2^4*x3^2 + x1^4*x3^12 + x1^4*x3^4 + x1^3*x2^19 + x1^3*x2^11 + x1^3*x2^3*x3^8 
                    + x1^3*x2^3*x3^4 + x1^3*x2^3 + x1^2*x2^22 + x1^2*x2^18*x3^2 + x1^2*x2^14 + x1^2*x2^10*x3^2
                    + x1^2*x2^6*x3^8 + x1^2*x2^6*x3^4 + x1^2*x2^2*x3^10 + x1^2*x2^2*x3^6 + x1*x2^25 
                    + x1*x2^17*x3^4 + x1*x2^17 + x1*x2^9*x3^8 + x1*x2^5*x3^2 + x1*x2*x3^12 + x1*x2*x3^8 
                    + x2^28 + x2^24*x3^2 + x2^20*x3^4 + x2^16*x3^6 + x2^12*x3^8 + x2^8*x3^10 + x2^8*x3^2 
                    + x2^4*x3^12 + x2^4*x3^4 + x3^14;
                bool, x3 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 56:
            repeat
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H := x1^20 + x1^16*x2^8 + x1^16*x3^8 + x1^14*x2^4 + x1^14*x3^4 + x1^13*x2^2 
                    + x1^13*x3^2 + x1^10*x2^12 + x1^10*x2^8*x3^4 + x1^10*x2^4*x3^8 + x1^10*x2^4
                    + x1^10*x3^12 + x1^10*x3^4 + x1^9*x2^10 + x1^9*x2^8*x3^2 + x1^9*x2^2*x3^8 + x1^9*x3^10 
                    + x1^8*x2^4*x3^4 + x1^7*x2^4*x3^2 + x1^7*x2^2*x3^4 + x1^6*x2^20 + x1^6*x2^16*x3^4 
                    + x1^6*x2^4*x3^16 + x1^6*x2^2*x3^2 + x1^6*x3^20 + x1^5*x2^18 + x1^5*x2^16*x3^2 
                    + x1^5*x2^8*x3^2 + x1^5*x2^6*x3^4 + x1^5*x2^4*x3^6 + x1^5*x2^2*x3^16 + x1^5*x2^2*x3^8 
                    + x1^5*x3^18 + x1^4*x2^32 + x1^4*x2^8 + x1^4*x2^6*x3^2 + x1^4*x2^2*x3^6 + x1^4*x3^32 
                    + x1^4*x3^8 + x1^3*x2^12*x3^2 + x1^3*x2^10*x3^4 + x1^3*x2^6 + x1^3*x2^4*x3^10 
                    + x1^3*x2^2*x3^12 + x1^3*x3^6 + x1^2*x2^28 + x1^2*x2^24*x3^4 + x1^2*x2^20*x3^8 
                    + x1^2*x2^20 + x1^2*x2^16*x3^12 + x1^2*x2^16*x3^4 + x1^2*x2^12*x3^16 + x1^2*x2^10*x3^2 
                    + x1^2*x2^8*x3^20 + x1^2*x2^4*x3^24 + x1^2*x2^4*x3^16 + x1^2*x2^2*x3^10 + x1^2*x3^28 
                    + x1^2*x3^20 + x1*x2^26 + x1*x2^24*x3^2 + x1*x2^18*x3^8 + x1*x2^16*x3^10 + x1*x2^16*x3^2 
                    + x1*x2^14*x3^4 + x1*x2^12*x3^6 + x1*x2^10*x3^16 + x1*x2^10*x3^8 + x1*x2^8*x3^18 
                    + x1*x2^8*x3^10 + x1*x2^8*x3^2 + x1*x2^6*x3^12 + x1*x2^6*x3^4 + x1*x2^4*x3^14 
                    + x1*x2^4*x3^6 + x1*x2^2*x3^24 + x1*x2^2*x3^16 + x1*x2^2*x3^8 + x1*x3^26 + x2^40 
                    + x2^32*x3^8 + x2^20*x3^4 + x2^14*x3^2 + x2^10*x3^6 + x2^8*x3^32 + x2^6*x3^10 + x2^4*x3^20
                    + x2^4*x3^4 + x2^2*x3^14 + x3^40;
                bool, x1 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        when 60:
            repeat
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := PolynomialRing(FF).1;
                H := x1^48 + x1^41*x2 + x1^36*x2^4 + x1^36*x3^2 + x1^35*x2^3 + x1^34*x2^2 
                    + x1^33*x2^9 + x1^33*x2*x3^4 + x1^33*x2 + x1^32*x2^16 + x1^32*x2^4*x3^2 + x1^32*x3^8 
                    + x1^27*x2^3 + x1^26*x2^2 + x1^24*x2^8 + x1^24*x3^4 + x1^22*x2^2*x3^2 + x1^21*x2^5 
                    + x1^20*x2^4 + x1^20*x3^2 + x1^19*x2^11 + x1^19*x2^3*x3^4 + x1^19*x2^3 + x1^18*x2^10 
                    + x1^18*x2^6*x3^2 + x1^18*x2^2*x3^4 + x1^17*x2^9 + x1^17*x2*x3^4 + x1^16*x2^32 
                    + x1^16*x2^8*x3^4 + x1^16*x2^4*x3^2 + x1^16*x3^16 + x1^15*x2^7 + x1^14*x2^6 
                    + x1^14*x2^2*x3^2 + x1^13*x2*x3^2 + x1^12*x2^12 + x1^12*x2^8*x3^2 + x1^12*x2^4*x3^4 
                    + x1^12*x2^4 + x1^12*x3^6 + x1^11*x2^19 + x1^11*x2^11 + x1^11*x2^3*x3^8 + x1^11*x2^3*x3^4
                    + x1^11*x2^3 + x1^10*x2^18 + x1^10*x2^10 + x1^10*x2^2*x3^8 + x1^9*x2^33 + x1^9*x2^17 
                    + x1^9*x2^9*x3^4 + x1^9*x2^5*x3^2 + x1^9*x2*x3^16 + x1^9*x2*x3^8 + x1^9*x2*x3^4 
                    + x1^8*x2^24 + x1^8*x2^16*x3^4 + x1^8*x2^12*x3^2 + x1^8*x2^8*x3^8 + x1^8*x2^8 
                    + x1^8*x2^4*x3^6 + x1^8*x3^12 + x1^8*x3^4 + x1^7*x2^15 + x1^7*x2^7*x3^4 + x1^7*x2^7 
                    + x1^6*x2^18*x3^2 + x1^6*x2^14 + x1^6*x2^6*x3^4 + x1^6*x2^6 + x1^6*x2^2*x3^10 
                    + x1^6*x2^2*x3^6 + x1^5*x2^21 + x1^5*x2^9*x3^2 + x1^5*x2^5*x3^8 + x1^5*x2*x3^6 
                    + x1^4*x2^36 + x1^4*x2^32*x3^2 + x1^4*x2^20 + x1^4*x2^16*x3^2 + x1^4*x2^12*x3^4 
                    + x1^4*x2^12 + x1^4*x2^8*x3^6 + x1^4*x2^4*x3^16 + x1^4*x2^4*x3^8 + x1^4*x2^4*x3^4 
                    + x1^4*x3^18 + x1^4*x3^10 + x1^3*x2^35 + x1^3*x2^27 + x1^3*x2^19*x3^4 + x1^3*x2^19 
                    + x1^3*x2^11*x3^8 + x1^3*x2^11*x3^4 + x1^3*x2^11 + x1^3*x2^3*x3^16 + x1^3*x2^3*x3^12 
                    + x1^3*x2^3*x3^8 + x1^3*x2^3*x3^4 + x1^2*x2^34 + x1^2*x2^26 + x1^2*x2^22*x3^2 
                    + x1^2*x2^18*x3^4 + x1^2*x2^14*x3^2 + x1^2*x2^10*x3^8 + x1^2*x2^6*x3^10 + x1^2*x2^6*x3^6 
                    + x1^2*x2^2*x3^16 + x1^2*x2^2*x3^12 + x1*x2^41 + x1*x2^33*x3^4 + x1*x2^33 + x1*x2^17*x3^4
                    + x1*x2^13*x3^2 + x1*x2^9*x3^16 + x1*x2^9*x3^8 + x1*x2^9*x3^4 + x1*x2^5*x3^6 
                    + x1*x2*x3^20 + x1*x2*x3^16 + x2^48 + x2^36*x3^2 + x2^32*x3^8 + x2^24*x3^4 + x2^20*x3^2 
                    + x2^16*x3^16 + x2^12*x3^6 + x2^8*x3^12 + x2^8*x3^4 + x2^4*x3^18 + x2^4*x3^10 + x3^24;
                bool, x3 := HasRoot(H);
            until bool and x1 ne 0 and x2 ne 0 and x3 ne 0;
        else
            require false: "Argument 2 must be in {5,8,12,13,17,24,28,40,44,56,60} in characteristic 2.";
        end case;
        xx := [x1,x2,x3];
    else
        require false: "Not implemented for odd characteristic.";
    end if;
    if AbsolutelySimple then
        C := HyperellipticCurveFromAffineLevel2ThetaNullPoint(xx);
        chi := FrobeniusCharacteristicPolynomial(C);
        if not IsIrreducible(chi) or QuarticCMFieldType(NumberField(chi)) eq [2,2] then
            return RandomAffineLevel2ThetaNullPointWithRM(FF,D);
        end if;
    end if;
    return xx;
end intrinsic;

intrinsic RandomLevel2ThetaNullPointWithRM(FF::FldFin,D::RngIntElt : AbsolutelySimple := true) -> SeqEnum
    {}
    require Characteristic(FF) ne 2 : "Argument 1 must not have characteristic 2.";
    require D gt 0 and D mod 4 in {0,1} and not IsSquare(D) : "Argument 2 must be a real discriminant";
    require D in {1,4,5,8,9,12,13,16,17,20,24,28,32,40,44,48,52,56,60}: // -- error in nonmaximal 68 
        "Argument 2 must be in " * Sprint({1,4,5,8,9,12,13,16,17,20,24,28,32,40,44,48,52,56,60}) * ".";
    H := Level2ThetaNullHumbertPolynomial(FF,D);
    a00 := 1; c00 := 1;
    repeat 
        repeat
            a01 := PolynomialRing(FF).1;
            a10 := Random(FF);
            a11 := Random(FF);
            bool, a01 := HasRoot(Evaluate(H,[a00,a01,a10,a11]));
        until bool;
        c01, c10, c11 := Explode([a01^2,a10^2,a11^2]);
    until 
        c00*c11 ne c01*c10 and
        c00*c01 ne c10*c11 and
        c00*c10 ne c01*c11 and
        c00 + c01 + c10 + c11 ne 0 and 
        c00 + c01 - c10 - c11 ne 0 and 
        c00 - c01 - c10 + c11 ne 0 and 
        c00 - c01 + c10 - c11 ne 0;
    xx := [a00,a01,a10,a11];
    if AbsolutelySimple then
        ee := Level2ThetaNullPointToRosenhainInvariants(xx);
        C := HyperellipticCurveFromRosenhainInvariants(ee);
        chi := FrobeniusCharacteristicPolynomial(C);
        if not IsIrreducible(chi) or QuarticCMFieldType(NumberField(chi)) eq [2,2] then
            return RandomLevel2ThetaNullPointWithRM(FF,D);
        end if;
    end if;
    return xx;
end intrinsic;

intrinsic RandomRosenhainInvariantsWithRM(FF::FldFin,D::RngIntElt :
    AbsolutelySimple := true) -> SeqEnum
    {}
    require D gt 0 and D mod 4 in {0,1} and D gt 1 :
        "Argument 2 must be a real discriminant greater than 1";
    require Characteristic(FF) ne 2 :
        "Argument 1 must not have characteristic 2.";
    H := RosenhainHumbertPolynomial(FF,D);
    repeat
        e1 := PolynomialRing(FF).1;
        e2 := Random(FF);
        e3 := Random(FF);
        bool, e1 := HasRoot(Evaluate(H,[e1,e2,e3]));
        ee := bool select [e1,e2,e3] else [0,0,0];
    until bool
        and &and[ ee[i]-ee[j] ne 0 : i, j in [1..3] | i lt j ]
        and &and[ ee[i] - 1 ne 0 : i in [1..3] ]
        and &and[ ee[i] ne 0 : i in [1..3] ];
    if AbsolutelySimple then
        C := HyperellipticCurveFromRosenhainInvariants(ee);
        chi := FrobeniusCharacteristicPolynomial(C);
        if not IsIrreducible(chi) or QuarticCMFieldType(NumberField(chi)) eq [2,2] then
            return RandomRosenhainInvariantsWithRM(FF,D);
        end if;
    end if;
    return ee;
end intrinsic;

/*
The Satake power sum invariants for D = 0 mod 4 is given in terms of (t1,t2,t3) by:

  [
    (15*t1^2 - 36*t2)/(2*t1^2),
    (-15*t1^3 + 54*t1*t2 - 81*t3)/(t1^3),
    (-4215*t1^5 + 27720*t1^3*t2 - 25920*t1^2*t3 - 45360*t1*t2^2 + 77760*t1 + 77760*t2*t3 + 77760*t3)/(64*t1^5),
    (2955*t1^6 - 22005*t1^4*t2 + 10935*t1^4 + 24624*t1^3*t3 + 44712*t1^2*t2^2 - 52488*t1^2*t2 -  23328*t1^2 -
    93312*t1*t2*t3 + 46656*t1*t3 - 11664*t2^3 + 34992*t2^2 + 139968*t2 + 69984*t3^2 + 139968)/(32*t1^6)
  ]

on descending to s2 = t1^2 and s4 = t1*t3, this gives:

  [ 
    (15*s2 - 36*t2)/(2*s2),
    (-15*s2^2 + 54*s2*t2 - 81*s3)/s2^2,
    (-4215*s2^3 + 27720*s2^2*t2 - 45360*s2*t2^2 - 25920*s2*s3 + 77760*s2 + 77760*t2*s3 + 77760*s3)/(64*s2^3),
    (2955*s2^4 - 22005*s2^3*t2 + 10935*s2^3 + 44712*s2^2*t2^2 - 52488*s2^2*t2 + 24624*s2^2*s3 - 23328*s2^2 -
    11664*s2*t2^3 + 34992*s2*t2^2 - 93312*s2*t2*s3 + 139968*s2*t2 + 46656*s2*s3 + 139968*s2 + 69984*s3^2)/(32*s2^4)
  ]

This result is applied to SatakeToIgusaInvariants and reduced modulo p (= 3 or 5).
*/

function SatakeToIgusaInvariantsParametrization0Characteristic3(tt)
    s2, t2, s4 := Explode(tt);
    return [
        s2 * (s2 - t2 + 1) * (s2^2 - s2*t2 - s2 - s4),
        s2 * (s2 - t2 + 1) * (s2^2 - s2*t2 - s2 - s4) *
        (s2^4 - s2^3*t2 + s2^3 - s2^2*t2^2 + s2^2 + s2*t2^3 - s2*t2^2 - s2*t2*s4 + s2*t2 - s2*s4 - s2 + t2^2*s4 - t2*s4 - s4^2),
        (s2^4 + s2^3*t2 + s2^2*t2^2 + s2^2*t2 + s2^2*s4 - s2^2 - s2*t2^2 - s2*t2*s4 - s2*t2 - s2*s4 - s2 + s4^2) *      
        (s2^8 + s2^7*t2 - s2^7 + s2^6*t2^2 - s2^6*s4 - s2^5*t2^3 - s2^5*t2*s4 - s2^5*t2 - s2^5 - s2^4*t2^4 
        + s2^4*t2^3 + s2^4*t2 + s2^4*s4^2 + s2^4 - s2^3*t2^5 + s2^3*t2^3*s4 + s2^3*t2^2 + s2^2*t2^4*s4 + s2^2*t2^4 
        - s2^2*t2^3 - s2^2*t2*s4 - s2^2*t2 + s2^2 - s2*t2^3*s4^2 + s2*s4^3 + s2*s4^2 - s4^4),
        (s2 - t2 + 1) * (s2^2 - s2*t2 - s2 - s4) * 
        -s2 * (s2^10*t2^2 - s2^10*s4 - s2^9 + s2^7*t2^5 - s2^7*t2^3*s4 - s2^6*s4^3 + s2^6 +  s2^4*t2^8 
        - s2^4*t2^6*s4 - s2^4*t2^2*s4^3 - s2^4*t2^2 + s2^4*s4^4 + s2^4*s4 + s2^3*t2^6 + s2^3*t2^3*s4^3 
        + s2^3*t2^3 + s2^3 + s2*t2^5*s4^3 - s2*t2^3*s4^4 - s2*t2^2*s4^3 + s2*s4^4 + s4^6),
        -s2^2 * (s2 - t2 + 1)^6 * (s2^2 - s2*t2 - s2 - s4)^6 ];
end function;

function SatakeToIgusaInvariantsParametrization0Characteristic5(tt)
    s2, t2, s4 := Explode(tt);
    return [
	s2^2*t2 + 2*s2^2*s4 + s2^2 + s2*t2^2 + 2*s2*t2*s4 + 4*s2*t2 + 3*s2*s4 + 4*s2 + s4^2,
	4*s2^7*t2 + s2^6*t2^2 + 4*s2^5*t2^3 + 4*s2^5*t2*s4 + 3*s2^5*t2 + s2^4*t2^4 + 2*s2^4*t2^2*s4 + 4*s2^4*t2*s4 + 
        3*s2^4*t2 + s2^4*s4^2 + s2^4*s4 + 4*s2^4 + 4*s2^3*t2^5 + 2*s2^3*t2^3*s4 + s2^3*t2^3 + 3*s2^3*t2^2*s4 + 
        3*s2^3*t2*s4^2 + 3*s2^3*t2*s4 + 3*s2^3*t2 + 3*s2^3*s4^2 + 3*s2^3*s4 + 2*s2^3 + 4*s2^2*t2^4*s4 + 4*s2^2*t2^4 + 
        4*s2^2*t2^3*s4 + 2*s2^2*t2^3 + 3*s2^2*t2^2*s4^2 + 2*s2^2*t2^2*s4 + s2^2*t2^2 + 3*s2^2*t2*s4 + 3*s2^2*t2 + 
        s2^2*s4^3 + 4*s2^2*s4^2 + s2^2*s4 + 4*s2^2 + s2*t2^3*s4^2 + 2*s2*t2^2*s4^2 + s2*t2*s4^3 + s2*t2*s4^2 + 
        4*s2*s4^3 + 2*s2*s4^2 + 4*s4^4,
	4*s2^11*t2 + 4*s2^10*t2^2 + 4*s2^10*s4 + 4*s2^9*t2^2 + 3*s2^9*t2*s4 + s2^9*t2 + 4*s2^8*t2*s4 + s2^8*t2 + s2^8*s4^2 +
        2*s2^8*s4 + 2*s2^7*t2^2 + 2*s2^7*s4^2 + 4*s2^6*t2^6 + 3*s2^6*t2^3 + s2^6*t2^2 + 4*s2^6*t2*s4^2 + 3*s2^6*t2*s4 + 
        s2^6*t2 + 2*s2^6*s4^3 + 3*s2^6*s4^2 + 3*s2^6 + 4*s2^5*t2^7 + 4*s2^5*t2^5*s4 + 2*s2^5*t2^4 + 3*s2^5*t2^3 + 
        s2^5*t2^2*s4^2 + 4*s2^5*t2^2*s4 + 3*s2^5*t2*s4^3 + s2^5*t2*s4^2 + 4*s2^5*t2*s4 + s2^5*t2 + s2^5*s4^2 + s2^5*s4 +
        s2^5 + 4*s2^4*t2^7 + 3*s2^4*t2^6*s4 + s2^4*t2^6 + 3*s2^4*t2^5 + 3*s2^4*t2^4 + 4*s2^4*t2^3*s4^2 + 4*s2^4*t2^3*s4 +
        4*s2^4*t2^3 + 2*s2^4*t2^2*s4^3 + 3*s2^4*t2^2*s4 + 3*s2^4*t2*s4^2 + 3*s2^4*t2 + 4*s2^4*s4^4 + 3*s2^4*s4^3 + 
        3*s2^4*s4^2 + 3*s2^4*s4 + 4*s2^4 + 4*s2^3*t2^6*s4 + 3*s2^3*t2^6 + s2^3*t2^5*s4^2 + 2*s2^3*t2^5*s4 + s2^3*t2^5 + 
        s2^3*t2^4*s4^2 + 3*s2^3*t2^4*s4 + 3*s2^3*t2^3*s4^3 + 4*s2^3*t2^3*s4^2 + 4*s2^3*t2^3*s4 + 3*s2^3*t2^2*s4^2 + 
        2*s2^3*t2^2*s4 + 2*s2^3*t2*s4^4 + s2^3*t2*s4^3 + s2^3*t2*s4^2 + 4*s2^3*t2*s4 + s2^3*t2 + s2^3*s4^4 + s2^3*s4^3 +
        3*s2^3*s4^2 + 2*s2^3*s4 + 2*s2^3 + s2^2*t2^5*s4^2 + 2*s2^2*t2^4*s4^3 + 2*s2^2*t2^4*s4^2 + s2^2*t2^3*s4^2 + 
        2*s2^2*t2^2*s4^4 + 3*s2^2*t2^2*s4^3 + 3*s2^2*t2^2*s4^2 + 2*s2^2*t2*s4^4 + s2^2*t2*s4^3 + 4*s2^2*t2*s4^2 + 
        3*s2^2*s4^5 + s2^2*s4^4 + 3*s2^2*s4^3 + 4*s2^2*s4^2 + 4*s2*t2^3*s4^4 + s2*t2^2*s4^4 + 3*s2*t2*s4^5 + 
        s2*t2*s4^4 + 2*s2*s4^5 + 3*s4^6,
	s2^14*t2^2 + 3*s2^13*t2^3 + s2^13*t2^2 + 2*s2^13*t2*s4 + s2^13*t2 + 3*s2^12*t2^4 + 2*s2^12*t2^3 + s2^12*t2^2*s4 + 
        4*s2^12*t2^2 + 4*s2^12*t2*s4 + 4*s2^12*t2 + 2*s2^12*s4^2 + s2^12*s4 + s2^11*t2^5 + s2^11*t2^4 + s2^11*t2^3*s4 + 
        s2^11*t2^3 + 3*s2^11*t2^2 + 2*s2^11*t2*s4 + s2^11*t2 + 3*s2^11*s4^2 + 4*s2^11*s4 + 2*s2^10*t2^4*s4 + 
        3*s2^10*t2^4 + s2^10*t2^3*s4 + 4*s2^10*t2^3 + 2*s2^10*t2^2*s4^2 + s2^10*t2*s4^2 + s2^10*t2*s4 + s2^10*t2 + 
        4*s2^10*s4^3 + 3*s2^10*s4 + s2^9*t2^7 + 4*s2^9*t2^3*s4^2 + 3*s2^9*t2^3*s4 + 3*s2^9*t2^3 + 4*s2^9*t2^2*s4 + 
        s2^9*t2*s4^3 + 3*s2^9*t2*s4^2 + 4*s2^9*t2*s4 + 2*s2^9*t2 + 3*s2^9*s4^3 + 3*s2^9*s4^2 + 2*s2^9*s4 + 3*s2^8*t2^8 +
        s2^8*t2^7 + 2*s2^8*t2^6*s4 + s2^8*t2^6 + 3*s2^8*t2^2*s4^3 + 2*s2^8*t2^2*s4^2 + 3*s2^8*t2^2*s4 + s2^8*t2*s4^3 + 
        2*s2^8*t2*s4 + 2*s2^8*t2 + s2^8*s4^4 + s2^8*s4^3 + 3*s2^8*s4^2 + 2*s2^8*s4 + 3*s2^8 + 3*s2^7*t2^9 + 2*s2^7*t2^8 
        + s2^7*t2^7*s4 + 4*s2^7*t2^7 + 4*s2^7*t2^6*s4 + 4*s2^7*t2^6 + 2*s2^7*t2^5*s4^2 + s2^7*t2^5*s4 + 3*s2^7*t2^4 + 
        2*s2^7*t2^3*s4 + s2^7*t2^3 + s2^7*t2^2*s4^2 + s2^7*t2^2*s4 + 4*s2^7*t2^2 + s2^7*t2*s4^4 + 3*s2^7*t2*s4^3 + 
        3*s2^7*t2*s4^2 + 4*s2^7*t2*s4 + 2*s2^7*t2 + 3*s2^7*s4^4 + 3*s2^7*s4^3 + 4*s2^7*s4^2 + s2^7*s4 + 3*s2^7 + 
        s2^6*t2^10 + s2^6*t2^9 + s2^6*t2^8*s4 + s2^6*t2^8 + 3*s2^6*t2^7 + 2*s2^6*t2^6*s4 + s2^6*t2^6 + 3*s2^6*t2^5*s4^2 +
        4*s2^6*t2^5*s4 + 4*s2^6*t2^5 + 3*s2^6*t2^4*s4 + s2^6*t2^4 + 4*s2^6*t2^3*s4^2 + s2^6*t2^3*s4 + 4*s2^6*t2^3 + 
        2*s2^6*t2^2*s4^3 + 3*s2^6*t2^2*s4 + 2*s2^6*t2^2 + s2^6*t2*s4^4 + s2^6*t2*s4^3 + 4*s2^6*t2*s4 + 2*s2^6*s4^5 + 
        s2^6*s4^4 + 4*s2^6*s4^3 + 4*s2^6*s4^2 + 3*s2^6 + 2*s2^5*t2^9*s4 + 3*s2^5*t2^9 + s2^5*t2^8*s4 + 4*s2^5*t2^8 + 
        2*s2^5*t2^7*s4^2 + s2^5*t2^6*s4^2 + s2^5*t2^6*s4 + 4*s2^5*t2^5*s4^3 + 4*s2^5*t2^5 + s2^5*t2^4*s4^2 + 
        2*s2^5*t2^4*s4 + s2^5*t2^4 + 3*s2^5*t2^3*s4^3 + 2*s2^5*t2^3*s4^2 + s2^5*t2^3*s4 + 3*s2^5*t2^3 + 4*s2^5*t2^2*s4^4 +
        2*s2^5*t2^2*s4^2 + 2*s2^5*t2^2*s4 + 2*s2^5*t2*s4^4 + 4*s2^5*t2*s4^3 + 2*s2^5*t2*s4^2 + 3*s2^5*t2*s4 + 
        3*s2^5*s4^4 + s2^5*s4^3 + 3*s2^5*s4^2 + 3*s2^5*s4 + 3*s2^5 + 4*s2^4*t2^8*s4^2 + 3*s2^4*t2^8*s4 + 3*s2^4*t2^8 + 
        4*s2^4*t2^7*s4 + 3*s2^4*t2^7 + s2^4*t2^6*s4^3 + 3*s2^4*t2^6*s4^2 + 2*s2^4*t2^6*s4 + s2^4*t2^6 + 3*s2^4*t2^5*s4^3 +
        2*s2^4*t2^5*s4^2 + 2*s2^4*t2^5*s4 + 4*s2^4*t2^5 + 2*s2^4*t2^4*s4^3 + s2^4*t2^4*s4^2 + s2^4*t2^3*s4^4 + 
        4*s2^4*t2^3*s4^3 + s2^4*t2^3*s4^2 + s2^4*t2^3*s4 + s2^4*t2^3 + 3*s2^4*t2^2*s4^5 + s2^4*t2^2*s4^3 + 
        4*s2^4*t2^2*s4^2 + 3*s2^4*t2^2*s4 + s2^4*t2^2 + 2*s2^4*t2*s4^5 + 3*s2^4*t2*s4^4 + 2*s2^4*t2*s4^3 + 
        3*s2^4*t2*s4^2 + 4*s2^4*t2*s4 + 2*s2^4*t2 + 4*s2^4*s4^6 + 4*s2^4*s4^5 + 4*s2^4*s4^4 + 2*s2^4*s4^3 + 4*s2^4*s4 + 
        3*s2^4 + 3*s2^3*t2^7*s4^3 + 2*s2^3*t2^7*s4^2 + s2^3*t2^6*s4^3 + s2^3*t2^6*s4^2 + s2^3*t2^5*s4^4 + 
        4*s2^3*t2^5*s4^3 + 4*s2^3*t2^5*s4^2 + 4*s2^3*t2^4*s4^4 + 2*s2^3*t2^4*s4^3 + 4*s2^3*t2^3*s4^5 + 3*s2^3*t2^3*s4^4 +
        s2^3*t2^3*s4^3 + 4*s2^3*t2^2*s4^5 + 2*s2^3*t2^2*s4^4 + 4*s2^3*t2^2*s4^3 + 4*s2^3*t2^2*s4^2 + 2*s2^3*t2*s4^6 + 
        s2^3*t2*s4^5 + s2^3*t2*s4^3 + 2*s2^3*t2*s4^2 + 3*s2^3*s4^6 + 2*s2^3*s4^5 + 4*s2^3*s4^4 + 3*s2^3*s4^2 + 
        s2^2*t2^6*s4^4 + 4*s2^2*t2^5*s4^4 + 4*s2^2*t2^4*s4^5 + 4*s2^2*t2^4*s4^4 + 2*s2^2*t2^3*s4^5 + 2*s2^2*t2^3*s4^4 + 
        2*s2^2*t2^2*s4^6 + 2*s2^2*t2^2*s4^5 + s2^2*t2^2*s4^4 + 2*s2^2*t2*s4^5 + 4*s2^2*s4^7 + 3*s2^2*s4^6 + 3*s2^2*s4^5 +
        2*s2^2*s4^4 + 4*s2*t2^3*s4^6 + 2*s2*t2^2*s4^6 + 4*s2*t2*s4^7 + s2*s4^7 + 4*s2*s4^6 + 3*s4^8,
	3*s2^20 + s2^19*t2 + 3*s2^18*t2^2 + 4*s2^18*s4 + 3*s2^18 + 4*s2^17*t2*s4 + 3*s2^17*s4 + s2^15*t2^5 + 2*s2^14*t2^6 + 
        s2^13*t2^7 + 3*s2^13*t2^5*s4 + s2^13*t2^5 + 3*s2^12*t2^6*s4 + s2^12*t2^5*s4 + 3*s2^10*t2^10 + 4*s2^10*s4^5 + 
        3*s2^10 + s2^9*t2^11 + 3*s2^9*t2*s4^5 + s2^9*t2 + 3*s2^8*t2^12 + 4*s2^8*t2^10*s4 + 3*s2^8*t2^10 + 
        4*s2^8*t2^2*s4^5 + 3*s2^8*t2^2 + 2*s2^8*s4^6 + 4*s2^8*s4^5 + 4*s2^8*s4 + 3*s2^8 + 4*s2^7*t2^11*s4 + 
        3*s2^7*t2^10*s4 + 2*s2^7*t2*s4^6 + 4*s2^7*t2*s4 + 4*s2^7*s4^6 + 3*s2^7*s4 + 4*s2^5*t2^5*s4^5 + 3*s2^5*s4^5 + 
        3*s2^4*t2^6*s4^5 + s2^4*t2*s4^5 + 4*s2^3*t2^7*s4^5 + 2*s2^3*t2^5*s4^6 + 4*s2^3*t2^5*s4^5 + 3*s2^3*t2^2*s4^5 + 
        4*s2^3*s4^6 + 3*s2^3*s4^5 + 2*s2^2*t2^6*s4^6 + 4*s2^2*t2^5*s4^6 + 4*s2^2*t2*s4^6 + 3*s2^2*s4^6
	];
end function;

/*

The Satake power sum invariants for D = 1 mod 8 is given in terms of (t1,t2,t3) by:

  [
    30*t1^2 - 72*t2,
    120*t1^3 - 432*t1*t2 + 648*t3,
    (4215*t1^5 - 27720*t1^3*t2 + 25920*t1^2*t3 + 45360*t1*t2^2 - 77760*t2*t3 + 77760*t5)/2,
    5910*t1^6 - 44010*t1^4*t2 + 49248*t1^3*t3 + 89424*t1^2*t2^2 - 186624*t1*t2*t3 + 46656*t1*t5 - 23328*t2^3 + 139968*t3^2
  ]

This result is applied to SatakeToIgusaInvariants and reduced modulo p (= 3 or 5).
*/

function SatakeToIgusaInvariantsParametrization5Characteristic3(tt)
    t1, t2, t3, t5 := Explode(tt);
    return [
        -t1 * (t1^5 + t1^3*t2 - t1^2*t3 + t1*t2^2 + t2*t3 + t5),
        (t1^5 + t1^3*t2 - t1^2*t3 + t1*t2^2 + t2*t3 + t5) * 
        (t1^7 - t1^5*t2 - t1^3*t2^2 - t1^2*t2*t3 - t1^2*t5 + t1*t2^3 - t1*t3^2 + t2^2*t3 + t2*t5),
        -(t1^3 - t1*t2 - t3) * 
        (t1^15 + t1^12*t3 - t1^10*t2*t3 - t1^10*t5 + t1^9*t2^3 - t1^9*t3^2 +
        2*t1^8*t2*t5 + t1^7*t3*t5 - t1^6*t2^3*t3 - t1^6*t3^3 - t1^5*t5^2 +
        t1^4*t2^4*t3 + t1^4*t2^3*t5 + t1^4*t3^2*t5 + t1^3*t2^6 + t1^3*t2^3*t3^2 +
        2*t1^3*t2*t5^2 - t1^3*t3^4 + t1^2*t2^4*t5 + t1^2*t2*t3^2*t5 + t1^2*t3*t5^2 +
        2*t1*t2^3*t3*t5 - t1*t2^2*t5^2 + t1*t2*t3^4 - t1*t3^3*t5 + t2^3*t3^3 +
        t2^2*t3^2*t5 - t2*t3*t5^2 + t3^5 - t5^3),
        (t1^5 + t1^3*t2 - t1^2*t3 + t1*t2^2 + t2*t3 + t5) * 
        (t1^16*t3 - t1^15*t2^2 + t1^10*t2^3*t3 + t1^10*t3^3 - t1^9*t2^5 +
        2*t1^7*t3^4 + t1^6*t2^2*t3^3 + t1^4*t2^6*t3 - t1^4*t2^3*t3^3 +
        t1^4*t5^3 - t1^3*t2^8 + t1*t2^3*t3^4 - t1*t3^6 + t1*t3*t5^3 - t2^5*t3^3 - t2^2*t5^3),
        (t1^5 + t1^3*t2 - t1^2*t3 + t1*t2^2 + t2*t3 + t5)^6 ];
end function;

function SatakeToIgusaInvariantsParametrization5Characteristic5(tt)
    t1, t2, t3, t5 := Explode(tt);
    return [
	t1^3*t3 + t1*t2*t3 + 2*t1*t5 + 3*t3^2,
	t1^10*t2 + 4*t1^8*t2^2 + t1^7*t2*t3 + t1^6*t2^3 + 4*t1^6*t3^2 + 3*t1^5*t2^2*t3 + 3*t1^5*t2*t5 + 4*t1^4*t2^4 + 
        2*t1^4*t2*t3^2 + t1^4*t3*t5 + 3*t1^3*t2^3*t3 + t1^3*t2^2*t5 + 4*t1^3*t3^3 + t1^2*t2^5 + 2*t1^2*t2^2*t3^2 + 
        t1^2*t5^2 + t1*t2^4*t3 + 3*t1*t2^3*t5 + 4*t1*t2*t3^3 + 3*t1*t3^2*t5 + 4*t2^3*t3^2 + 4*t2^2*t3*t5 + t2*t5^2 + 
        t3^4,
	3*t1^16*t2 + 3*t1^15*t3 + 3*t1^14*t2^2 + t1^13*t2*t3 + 2*t1^12*t3^2 + 3*t1^11*t2*t5 + t1^10*t3*t5 + 2*t1^9*t2^2*t5 +
        4*t1^9*t3^3 + 3*t1^7*t2^3*t5 + t1^7*t2*t3^3 + 4*t1^7*t3^2*t5 + 3*t1^6*t2^6 + 4*t1^6*t2^2*t3*t5 + 3*t1^6*t3^4 + 
        3*t1^5*t2^5*t3 + 2*t1^5*t2^4*t5 + 4*t1^5*t2^2*t3^3 + 4*t1^5*t2*t3^2*t5 + 3*t1^4*t2^7 + 2*t1^4*t2^3*t3*t5 + 
        4*t1^4*t2*t3^4 + 2*t1^4*t3^3*t5 + t1^3*t2^6*t3 + 3*t1^3*t2^5*t5 + t1^3*t2^3*t3^3 + t1^3*t2^2*t3^2*t5 + t1^3*t3^5
        + 4*t1^3*t5^3 + 2*t1^2*t2^5*t3^2 + 2*t1^2*t2^4*t3*t5 + 4*t1^2*t2^2*t3^4 + 3*t1^2*t2*t3^3*t5 + 4*t1*t2^4*t3^3 + 
        t1*t2^3*t3^2*t5 + t1*t2*t3^5 + 4*t1*t2*t5^3 + 2*t1*t3^4*t5 + 3*t2^3*t3^4 + t2^2*t3^3*t5 + t3^6 + 2*t3*t5^3,
	t1^20*t2^2 + 2*t1^19*t2*t3 + 3*t1^18*t2^3 + 2*t1^18*t3^2 + t1^17*t2^2*t3 + 4*t1^17*t2*t5 + 3*t1^16*t2^4 + 
        4*t1^16*t3*t5 + t1^15*t2^3*t3 + 4*t1^15*t3^3 + t1^14*t2^5 + 2*t1^14*t2^2*t3^2 + 2*t1^14*t2*t3*t5 + 
        2*t1^13*t2^4*t3 + t1^13*t2^3*t5 + t1^13*t2*t3^3 + 4*t1^12*t2^3*t3^2 + 4*t1^12*t2^2*t3*t5 + t1^12*t2*t5^2 + 
        t1^12*t3^4 + 3*t1^11*t2^2*t3^3 + 2*t1^11*t2*t3^2*t5 + 3*t1^11*t3*t5^2 + t1^10*t2^7 + t1^10*t2*t3^4 + 
        3*t1^10*t3^3*t5 + 2*t1^9*t2^6*t3 + 3*t1^9*t2*t3*t5^2 + 2*t1^9*t3^5 + 3*t1^8*t2^8 + 2*t1^8*t2^5*t3^2 + 
        4*t1^8*t2*t3^3*t5 + t1^8*t3^2*t5^2 + t1^7*t2^7*t3 + 4*t1^7*t2^6*t5 + 2*t1^7*t2^2*t3*t5^2 + t1^7*t2*t5^3 + 
        2*t1^7*t3^4*t5 + 3*t1^6*t2^9 + 4*t1^6*t2^5*t3*t5 + t1^6*t2^2*t3^3*t5 + 2*t1^6*t2*t3^2*t5^2 + 4*t1^6*t3^6 + 
        3*t1^6*t3*t5^3 + t1^5*t2^8*t3 + 4*t1^5*t2^5*t3^3 + 3*t1^5*t2^3*t3*t5^2 + 3*t1^5*t2^2*t3^5 + 3*t1^5*t2^2*t5^3 + 
        t1^5*t2*t3^4*t5 + t1^4*t2^10 + 2*t1^4*t2^7*t3^2 + 2*t1^4*t2^6*t3*t5 + 4*t1^4*t2^3*t3^3*t5 + 2*t1^4*t2*t3^6 + 
        4*t1^4*t2*t3*t5^3 + t1^4*t3^5*t5 + 3*t1^4*t5^4 + 2*t1^3*t2^9*t3 + t1^3*t2^8*t5 + t1^3*t2^6*t3^3 + 
        2*t1^3*t2^4*t3*t5^2 + 4*t1^3*t2^3*t3^5 + 3*t1^3*t2^3*t5^3 + t1^3*t2^2*t3^4*t5 + 4*t1^3*t3^7 + 2*t1^3*t3^2*t5^3 +
        4*t1^2*t2^8*t3^2 + 4*t1^2*t2^7*t3*t5 + t1^2*t2^6*t5^2 + t1^2*t2^5*t3^4 + t1^2*t2^4*t3^3*t5 + 
        3*t1^2*t2^3*t3^2*t5^2 + 2*t1^2*t2^2*t3^6 + 4*t1^2*t2^2*t3*t5^3 + t1^2*t2*t3^5*t5 + 4*t1^2*t2*t5^4 + 
        2*t1^2*t3^4*t5^2 + 3*t1*t2^7*t3^3 + 2*t1*t2^6*t3^2*t5 + t1*t2^5*t3*t5^2 + 4*t1*t2^4*t3^5 + t1*t2^4*t5^3 + 
        2*t1*t2^3*t3^4*t5 + 4*t1*t2*t3^7 + 2*t1*t2*t3^2*t5^3 + 3*t1*t3^6*t5 + t1*t3*t5^4 + t2^6*t3^4 + 2*t2^5*t3^3*t5 + 
        4*t2^4*t3^2*t5^2 + 4*t2^3*t3^6 + 3*t2^3*t3*t5^3 + t2^2*t5^4 + 2*t2*t3^4*t5^2 + 3*t3^8 + 4*t3^3*t5^3,
	-(t1^5 + 2*t1^3*t2 + 3*t1^2*t3 + t1*t2^2 + 3*t2*t3 + 4*t5)^6
	];
end function;

intrinsic RandomIgusaInvariantsWithRM(FF::FldFin,D::RngIntElt :
    AbsolutelySimple := false) -> SeqEnum
    {}
    require D gt 0 and D mod 4 in {0,1} and D gt 1 :
        "Argument 2 must be a real discriminant greater than 1";
    if Characteristic(FF) eq 2 then
        /*
        Let x = (x1,x2,x3) be a affine level 2 theta null point, and s = (s1,s2,s3)
        be the symmetric invariants of x.  The Igusa invariants of this curve are:

        JJ = ( 1 : 
               (s2^2/s3)^2 : 
               (s2^2/s3)^4 :
               ((s1^2*s3^4 + s2^8 + s2^6*s3)/s3^4)^2 : s3^2 ).

        Conversely the point s can be recovered from JJ over a finite field of
        characteristic 2 (extracting square roots). 
        */
        case D:
        when 5:
            // H := x1^4 + x2^4 + x3^4 + x1*x2*x3;
            // F := s1^4 + s3;
            repeat
                /*
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H := x1^4 + x2^4 + x3^4 + x1*x2*x3;
                bool, x1 := HasRoot(H);
                */
                s1 := Random(FF);
            until s1 ne 0;
            s2 := Random(FF);
            s3 := s1^4;
        when 8:
            // H := x1^2 + x2^2 + x3;
            // F := s1^5 + s1^3*s2 + s1^2*s2^2 + s1^2*s2 + s1^2*s3 + s1*s3 + s2*s3 + s3^2 + s3;
            bool := false;
            repeat
                /*
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := x1^2 + x2^2;
                */
                s1 := Random(FF); 
                s2 := Random(FF);
                if s1 eq 0 then
                    s3 := s2 + 1;
                    bool := true;
                elif s1^3 + s1*s2 + s2^2 + s2 eq 0 then 
                    s3 := s1^2 + s1 + s2 + 1;
                    bool := true;
                else
                    s3 := PolynomialRing(FF).1;
                    F := s1^5 + s1^3*s2 + s1^2*s2^2 + s1^2*s2 + s1^2*s3 + s1*s3 + s2*s3 + s3 + s3^2;
                    bool, s3 := HasRoot(F);
                end if;
            until bool and s3 ne 0;
        when 12:
            // H := x1^4 + x1*x2 + x2^4 + x3^2;
            bool := false;
            repeat
                /*
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := Sqrt(x1^4 + x1*x2 + x2^4);
                */
                s1 := Random(FF);
                s2 := Random(FF);
                s3 := PolynomialRing(FF).1;
                // Verify the different components:
                if s1^4 + s2 eq 0 then
                    F := s1^13 + s1^7 + s1^6*s3 + s1^5 + s1^3 + s1^2*s3 + s1*s3^2 + s3^3;
                elif s1^3 + s1*s2 + s2^2 + s2 eq 0 then
                    F := s1^7 + s1^5*s2 + s1^5 + s1^3 + s1^2*s2*s3
                        + s1^2*s3 + s1*s2^3 + s1*s2^2 + s1*s3^2 + s3^3;
                else
                    F := s1^10 + s1^7*s3 + s1^6*s2^2 + s1^6*s2 + s1^5*s2*s3
                        + s1^5*s3 + s1^4*s2^4 + s1^4*s2^2 + s1^3*s3 + s1^2*s2^3
                        + s1^2*s2*s3^2 + s1^2*s3^2 + s1*s2^3*s3 + s1*s2^2*s3
                        + s1*s3^3 + s2^5 + s2^3 + s3^4;
                end if;
                bool, s3 := HasRoot(F);
            until bool and s3 ne 0;
        when 13:
            bool := false;
            repeat
                /*
                x1 := Random(FF);
                x2 := Random(FF);
                x3 := Sqrt(x1^4 + x1*x2 + x2^4);
                */
                s1 := Random(FF);
                s3 := Random(FF);
                if s1^4 + s3 eq 0 then continue; end if;
                /*
                s2 := PolynomialRing(FF).1;
                F := s1^20 + s1^16*s3 + s1^12*s3 + s1^8*s3^2 + s1^4*s2^4 + s1^4*s3^4
                    + s1^4*s3^3 + s2^4*s3 + s3^5 + s3^4 + s3^3;
                bool, s2 := HasRoot(F);
                */
                s2 := Sqrt(Sqrt((s1^20 + s1^16*s3 + s1^12*s3 + s1^8*s3^2
                    + s1^4*s3^4 + s1^4*s3^3 + s3^5 + s3^4 + s3^3)/(s1^4 + s3)));
                bool := true;
            until bool and s3 ne 0;
        when 17:
            bool := false;
            repeat
                /*
                x1 := PolynomialRing(FF).1;
                x2 := Random(FF);
                x3 := Random(FF);
                H := x1^8 + x1^5*x2^7*x3 + x1^5*x2^3*x3 + x1^4*x2^16 + x1^4*x2^12*x3^4
                    + x1^4*x2^8 + x1^4*x2^4*x3^4 + x1^3*x2^13*x3^3 + x1^3*x2^9*x3^3
                    + x1^3*x2^5*x3^3 + x1^3*x2*x3^3 + x1^2*x2^10*x3^2 + x1*x2^19*x3
                    + x1*x2^15*x3 + x1*x2^7*x3^5 + x1*x2^3*x3^5 + x2^24 + x2^16*x3^4
                    + x2^8*x3^4 + x3^8;
                bool, x1 := HasRoot(H);
                if bool then
                    s1 := x1+x2+x3;
                    s2 := x1*x2+x1*x3+x2*x3;
                    s3 := x1*x2*x3;
                    bool and:= s3 ne 0;
                end if;
                */
                s1 := Random(FF); 
                s2 := PolynomialRing(FF).1;
                s3 := Random(FF);
                if s3 eq 0 then continue; end if;
                F := s1^40 + s1^34*(s2^2*s3 + s3) + s1^32*(s2^2*s3^3 + s2^2*s3 + s3^3) +
                    s1^30*(s2^6*s3 + s2^4*s3 + s2^2*s3^3 + s2^2*s3 + s3^5 + s3^4 + s3^3 + s3) + 
                    s1^28*(s2^8 + s2^4*s3^3 + s2^4 + s2^2*s3^5 + s2^2*s3^2 + s3^5 + s3^3) +
                    s1^26*(s2^8*s3 + s2^6*s3^3 + s2^6*s3 + s2^4*s3^4 + s2^4*s3^3 +
                    s2^4*s3^2 + s2^4*s3 + s2^2*s3^7 + s2^2*s3^5 + s2^2*s3^3 +
                    s2^2*s3^2 + s2^2*s3 + s3^8 + s3^7 + s3^5 + s3^3) +
                    s1^24*(s2^8*s3^4 + s2^8*s3^2 +
                    s2^6*s3^5 + s2^6*s3^2 + s2^4*s3^5 + s2^4*s3^4 + 
                    s2^4*s3^3 + s2^2*s3^7 + s2^2*s3^5 + s2^2*s3^4 + 
                    s2^2*s3^3 + s2^2*s3^2 + s3^9 + s3^7 + s3^4 + s3^3 + s3^2) +
                    s1^22*(s2^10*s3^3 + s2^8*s3^3 + 
                    s2^8*s3^2 + s2^8*s3 + s2^6*s3^5 + s2^6*s3^4 + 
                    s2^6*s3^3 + s2^6*s3^2 + s2^6*s3 + s2^4*s3^5 + 
                    s2^4*s3^2 + s2^2*s3^9 + s2^2*s3^8 + s2^2*s3^7 + 
                    s2^2*s3^6 + s2^2*s3^3 + s2^2*s3^2 + s3^9 + s3^4 + s3^3) +
                    s1^20*(s2^16 + s2^12 + s2^10*s3^3 + 
                    s2^10*s3 + s2^8*s3^5 + s2^8*s3^4 + s2^8 + 
                    s2^6*s3^7 + s2^6*s3^4 + s2^6*s3^3 + s2^6*s3 + 
                    s2^4*s3^8 + s2^4*s3^7 + s2^4*s3^6 + s2^4*s3^4 + 
                    s2^4 + s2^2*s3^9 + s2^2*s3^8 + s2^2*s3^7 + 
                    s2^2*s3^4 + s2^2*s3^3 + s3^11 + s3^10 + s3^8 + s3^5 + s3^4) +
                    s1^18*(s2^14*s3 + s2^12*s3^3 + 
                    s2^12*s3 + s2^10*s3^3 + s2^10*s3^2 + s2^8*s3^6 + 
                    s2^8*s3^5 + s2^8*s3^4 + s2^8*s3^2 + s2^6*s3^9 + 
                    s2^6*s3^6 + s2^6*s3^5 + s2^6*s3^3 + s2^6*s3^2 + 
                    s2^6*s3 + s2^4*s3^10 + s2^4*s3^8 + s2^4*s3^7 + 
                    s2^4*s3^2 + s2^4*s3 + s2^2*s3^8 + s2^2*s3^5 + 
                    s2^2*s3^4 + s3^12 + s3^10 + s3^9 + s3^5 + s3^3) +
                    s1^16*(s2^12*s3^4 + s2^12*s3^3 + s2^12 + 
                    s2^10*s3^7 + s2^10*s3^5 + s2^10*s3^4 + s2^8*s3^8 +
                    s2^8*s3^6 + s2^8*s3^5 + s2^8*s3^4 + s2^8*s3^3 + 
                    s2^6*s3^7 + s2^6*s3^5 + s2^6*s3^3 + s2^4*s3^11 + 
                    s2^4*s3^8 + s2^4*s3^7 + s2^2*s3^9 + s2^2*s3^6 + 
                    s2^2*s3^3 + s3^12 + s3^9 + s3^8 + s3^7 + s3^6 + s3^5) +
                    s1^14*(s2^18*s3 + s2^14*s3^3 + s2^14*s3 +
                    s2^10*s3^6 + s2^10*s3^5 + s2^10*s3^4 + 
                    s2^10*s3^2 + s2^8*s3^6 + s2^8*s3^5 + s2^8*s3^2 + 
                    s2^8*s3 + s2^6*s3^11 + s2^6*s3^10 + s2^6*s3^8 + 
                    s2^4*s3^6 + s2^4*s3^4 + s2^4*s3^3 + s2^4*s3 + 
                    s2^2*s3^12 + s2^2*s3^11 + s2^2*s3^10 + s2^2*s3^8 +
                    s2^2*s3^6 + s2^2*s3^5 + s2^2*s3^4 + s2^2*s3^3 + 
                    s3^16 + s3^14 + s3^13 + s3^11 + s3^7 + s3^3) +
                    s1^12*(s2^20 + s2^18*s3 + s2^16*s3^4 + 
                    s2^16*s3^3 + s2^16 + s2^14*s3^5 + s2^14*s3^2 + 
                    s2^14*s3 + s2^12*s3^5 + s2^12*s3^3 + s2^12*s3^2 + 
                    s2^12 + s2^10*s3^9 + s2^10*s3^7 + s2^10*s3^5 + 
                    s2^10*s3^4 + s2^10*s3 + s2^8*s3^12 + s2^8*s3^10 + 
                    s2^8*s3^6 + s2^8*s3^5 + s2^8*s3^2 + s2^8 + 
                    s2^6*s3^13 + s2^6*s3^11 + s2^6*s3^10 + s2^6*s3^5 +
                    s2^6*s3^4 + s2^6*s3^3 + s2^6*s3^2 + s2^6*s3 + 
                    s2^4*s3^13 + s2^4*s3^12 + s2^4*s3^11 + s2^4*s3^9 +
                    s2^4*s3^8 + s2^4*s3^7 + s2^4*s3^5 + s2^2*s3^15 + 
                    s2^2*s3^11 + s2^2*s3^8 + s2^2*s3^7 + s2^2*s3^6 + 
                    s2^2*s3^5 + s2^2*s3^4 + s3^14 + s3^12 + 
                    s3^11 + s3^10 + s3^9 + s3^8 + s3^6 + s3^5) +
                    s1^10*(s2^20*s3 + s2^16*s3^4 + s2^16*s3^3 + 
                    s2^16*s3^2 + s2^14*s3^2 + s2^14*s3 + s2^12*s3^8 + 
                    s2^12*s3^7 + s2^12*s3^5 + s2^12*s3^3 + s2^12*s3 + 
                    s2^10*s3^8 + s2^10*s3^7 + s2^10*s3^6 + s2^10*s3^5 +
                    s2^10*s3^4 + s2^10*s3^3 + s2^8*s3^10 + s2^8*s3^8 +
                    s2^8*s3^6 + s2^8*s3^4 + s2^8*s3^2 + s2^6*s3^13 +
                    s2^6*s3^9 + s2^6*s3^8 + s2^6*s3^7 + s2^6*s3^6 + 
                    s2^6*s3^5 + s2^6*s3^3 + s2^6*s3^2 + s2^6*s3 + 
                    s2^4*s3^15 + s2^4*s3^10 + s2^4*s3^9 + s2^4*s3^8 + 
                    s2^4*s3^7 + s2^4*s3^6 + s2^2*s3^16 + s2^2*s3^14 + 
                    s2^2*s3^11 + s2^2*s3^10 + s2^2*s3^9 + s2^2*s3^8 + 
                    s2^2*s3^4 + s2^2*s3^3 + s3^17 + s3^16 + 
                    s3^14 + s3^13 + s3^9 + s3^8 + s3^5) + 
                    s1^8*(s2^24 + s2^20 + s2^18*s3^2 + s2^16*s3^4 + 
                    s2^14*s3^5 + s2^14*s3^4 + s2^14*s3^3 + s2^14*s3^2 + 
                    s2^14*s3 + s2^12*s3^4 + s2^12*s3^3 + s2^12 + 
                    s2^10*s3^11 + s2^10*s3^8 + s2^10*s3^2 + s2^8*s3^12 + 
                    s2^8*s3^10 + s2^8*s3^9 + s2^8*s3^8 + s2^8*s3^7 + 
                    s2^8*s3^5 + s2^8 + s2^6*s3^15 + s2^6*s3^9 + 
                    s2^6*s3^6 + s2^6*s3^5 + s2^6*s3^3 + s2^6*s3^2 + 
                    s2^4*s3^15 + s2^4*s3^14 + s2^4*s3^12 + s2^4*s3^10 + 
                    s2^4*s3^9 + s2^4*s3^8 + s2^4*s3^7 + s2^4*s3^6 + 
                    s2^4*s3^5 + s2^4*s3^3 + s2^2*s3^17 + s2^2*s3^14 + 
                    s2^2*s3^13 + s2^2*s3^10 + s2^2*s3^9 + s2^2*s3^8 + 
                    s2^2*s3^6 + s2^2*s3^5 + s2^2*s3^4 + s3^18 + s3^17 +
                    s3^15 + s3^12 + s3^11 + s3^10 + s3^6 + s3^5) +
                    s1^6*(s2^20*s3^2 + s2^18*s3^4 + s2^18*s3^3 + 
                    s2^16*s3^6 + s2^16*s3^2 + s2^14*s3^9 + s2^14*s3^8 + 
                    s2^14*s3^7 + s2^14*s3^3 + s2^12*s3^10 + s2^12*s3^8 + 
                    s2^12*s3^7 + s2^10*s3^13 + s2^10*s3^11 + s2^10*s3^10 +
                    s2^10*s3^9 + s2^10*s3^7 + s2^10*s3^6 + s2^10*s3^5 + 
                    s2^10*s3^4 + s2^10*s3^3 + s2^10*s3^2 + s2^8*s3^14 + 
                    s2^8*s3^13 + s2^8*s3^12 + s2^8*s3^11 + s2^8*s3^9 + 
                    s2^8*s3^7 + s2^8*s3^5 + s2^8*s3^4 + s2^6*s3^15 + 
                    s2^6*s3^14 + s2^6*s3^12 + s2^6*s3^9 + s2^6*s3^8 + 
                    s2^6*s3^4 + s2^6*s3^3 + s2^6*s3^2 + s2^4*s3^17 + 
                    s2^4*s3^16 + s2^4*s3^15 + s2^4*s3^14 + s2^4*s3^11 + 
                    s2^4*s3^5 + s2^4*s3^4 + s2^2*s3^19 + s2^2*s3^14 + 
                    s2^2*s3^11 + s2^2*s3^10 + s2^2*s3^8 + s2^2*s3^6 + 
                    s2^2*s3^5 + s2^2*s3^4 + s3^20 + s3^19 + s3^15 + 
                    s3^14 + s3^13 + s3^12 + s3^11 + s3^10 + s3^9 + s3^8 + s3^6) +
                    s1^4*(s2^22*s3^3 + s2^22*s3 + 
                    s2^20*s3^4 + s2^18*s3^7 + s2^18*s3^3 + s2^18*s3 + 
                    s2^16*s3^8 + s2^16*s3^6 + s2^16*s3^4 + s2^16*s3^3 + 
                    s2^14*s3^9 + s2^14*s3^7 + s2^14*s3^5 + s2^14*s3^4 + 
                    s2^14*s3^3 + s2^14*s3 + s2^12*s3^12 + s2^12*s3^11 + 
                    s2^12*s3^8 + s2^12*s3^6 + s2^12*s3^4 + s2^10*s3^11 + 
                    s2^10*s3^9 + s2^10*s3^6 + s2^10*s3^5 + s2^10*s3^4 + 
                    s2^10*s3 + s2^8*s3^16 + s2^8*s3^15 + s2^8*s3^13 + 
                    s2^8*s3^10 + s2^8*s3^9 + s2^8*s3^7 + s2^8*s3^3 + 
                    s2^6*s3^15 + s2^6*s3^14 + s2^6*s3^13 + s2^6*s3^10 + 
                    s2^6*s3^5 + s2^6*s3^3 + s2^4*s3^17 + s2^4*s3^14 + 
                    s2^4*s3^12 + s2^4*s3^10 + s2^4*s3^9 + s2^4*s3^8 + 
                    s2^4*s3^6 + s2^4*s3^4 + s2^2*s3^19 + s2^2*s3^18 + 
                    s2^2*s3^16 + s2^2*s3^15 + s2^2*s3^14 + s2^2*s3^13 + 
                    s2^2*s3^11 + s2^2*s3^9 + s2^2*s3^7 + s2^2*s3^6 + 
                    s2^2*s3^5 + s3^21 + s3^16 + s3^15 + s3^13 + 
                    s3^12 + s3^11 + s3^10 + s3^8 + s3^7 + s3^6) +
                    s1^2*(s2^22*s3^3 + s2^22*s3^2 + s2^20*s3^5 + s2^18*s3^7 + 
                    s2^18*s3^6 + s2^18*s3^4 + s2^18*s3^3 + s2^16*s3^2 + 
                    s2^14*s3^11 + s2^14*s3^10 + s2^14*s3^9 + s2^14*s3^8 + 
                    s2^14*s3^5 + s2^14*s3^4 + s2^14*s3^2 + s2^12*s3^13 + 
                    s2^12*s3^9 + s2^12*s3^8 + s2^12*s3^6 + s2^12*s3^5 + 
                    s2^10*s3^15 + s2^10*s3^14 + s2^10*s3^13 + s2^10*s3^10 + 
                    s2^10*s3^9 + s2^10*s3^7 + s2^10*s3^6 + s2^10*s3^3 + 
                    s2^8*s3^11 + s2^8*s3^10 + s2^8*s3^8 + s2^8*s3^6 + 
                    s2^8*s3^4 + s2^8*s3^2 + s2^6*s3^17 + s2^6*s3^16 + 
                    s2^6*s3^14 + s2^6*s3^13 + s2^6*s3^12 + s2^6*s3^9 + 
                    s2^6*s3^6 + s2^6*s3^5 + s2^6*s3^3 + s2^4*s3^19 + 
                    s2^4*s3^17 + s2^4*s3^16 + s2^4*s3^14 + s2^4*s3^13 + 
                    s2^4*s3^11 + s2^4*s3^10 + s2^4*s3^8 + s2^4*s3^7 + 
                    s2^4*s3^4 + s2^2*s3^21 + s2^2*s3^20 + s2^2*s3^19 + 
                    s2^2*s3^18 + s2^2*s3^13 + s2^2*s3^9 + s2^2*s3^7 + 
                    s2^2*s3^6 + s3^21 + s3^18 + s3^16 + s3^15 + s3^14 + s3^9 + s3^7) +
                    s2^26*s3 + s2^24*s3^4 + s2^22*s3^5 + 
                    s2^22*s3 + s2^20*s3^5 + s2^20*s3^3 + s2^18*s3^9 + s2^18*s3^6 + s2^16*s3^12 + 
                    s2^16*s3^10 + s2^16*s3^9 + s2^16*s3^8 + s2^16*s3^7 + s2^16*s3^6 + 
                    s2^16*s3^5 + s2^16*s3^3 + s2^14*s3^13 + s2^14*s3^11 + s2^14*s3^9 + 
                    s2^14*s3^8 + s2^14*s3^7 + s2^14*s3^6 + s2^14*s3^5 + s2^14*s3^4 + s2^14*s3 + 
                    s2^12*s3^13 + s2^12*s3^12 + s2^12*s3^9 + s2^12*s3^6 + s2^12*s3^3 + 
                    s2^10*s3^14 + s2^10*s3^11 + s2^10*s3^10 + s2^10*s3^9 + s2^10*s3^8 + 
                    s2^10*s3^6 + s2^10*s3^5 + s2^10*s3 + s2^8*s3^17 + s2^8*s3^14 + s2^8*s3^13 + 
                    s2^8*s3^11 + s2^8*s3^10 + s2^8*s3^8 + s2^8*s3^5 + s2^8*s3^4 + s2^8*s3^3 + 
                    s2^6*s3^19 + s2^6*s3^16 + s2^6*s3^14 + s2^6*s3^11 + s2^6*s3^4 + 
                    s2^4*s3^20 + s2^4*s3^19 + s2^4*s3^18 + s2^4*s3^17 + s2^4*s3^16 + 
                    s2^4*s3^12 + s2^4*s3^11 + s2^4*s3^9 + s2^4*s3^8 + s2^4*s3^5 + s2^2*s3^21 +
                    s2^2*s3^20 + s2^2*s3^19 + s2^2*s3^18 + s2^2*s3^16 + s2^2*s3^15 + 
                    s2^2*s3^14 + s2^2*s3^9 + s2^2*s3^7 + s2^2*s3^6 + s3^24 + s3^23 + s3^22 + 
                    s3^20 + s3^19 + s3^17 + s3^14 + s3^13 + s3^12 + s3^10 + s3^7;
                bool, s2 := HasRoot(F);
            until bool and s3 ne 0;
        when 24:
            bool := false;
            repeat
                s1 := Random(FF); 
                s2 := PolynomialRing(FF).1;
                s3 := Random(FF);
                if s3 eq 0 then continue; end if;
                F := s1^30 + s1^26*s2^2 + s1^25*s2^2 + s1^24*s2^4 + s1^24*s2^2 + s1^24*s3^2 + 
                    s1^23*s2^3 + s1^23*s2 + s1^23*s3^2 + s1^22*s2^4 + s1^22*s2^2*s3 + s1^22*s3 +
                    s1^21*s2^4 + s1^21*s2^2 + s1^21*s2*s3^2 + s1^20*s2^3*s3 + s1^20*s2^2*s3^2 + 
                    s1^20*s3^4 + s1^20*s3^3 + s1^20*s3^2 + s1^19*s2^6 + s1^19*s2^4 + s1^19*s3^2 +
                    s1^18*s2^8 + s1^18*s2^6 + s1^18*s2^4 + s1^18*s2^3 + s1^18*s2^2*s3^2 + 
                    s1^18*s2^2 + s1^18*s2*s3^3 + s1^18*s3^4 + s1^17*s2^7 + s1^17*s2^4*s3^2 + 
                    s1^17*s2^4 + s1^17*s2^3 + s1^17*s2^2*s3 + s1^17*s3^4 + s1^17*s3 + s1^16*s2^8 + 
                    s1^16*s2^6*s3 + s1^16*s2^6 + s1^16*s2^5*s3 + s1^16*s2^4*s3^2 + 
                    s1^16*s2^3*s3 + s1^16*s2^2*s3^2 + s1^16*s2^2*s3 + s1^16*s2*s3^2 + s1^16*s3^4 + 
                    s1^16*s3^2 + s1^15*s2^7 + s1^15*s2^6 + s1^15*s2^5*s3^2 + s1^15*s2^5 + 
                    s1^15*s2^4*s3^2 + s1^15*s2^4 + s1^15*s2^2*s3^4 + s1^15*s2^2*s3^2 + 
                    s1^15*s2*s3 + s1^15*s3^4 + s1^15*s3^3 + s1^14*s2^10 + s1^14*s2^7*s3 + 
                    s1^14*s2^6*s3 + s1^14*s2^6 + s1^14*s2^5*s3 + s1^14*s2^5 + s1^14*s2^4*s3^3 + 
                    s1^14*s2^4*s3 + s1^14*s2^4 + s1^14*s2^2*s3^4 + s1^14*s2*s3^3 + s1^14*s3^2 + 
                    s1^13*s2^9 + s1^13*s2^5*s3^2 + s1^13*s2^5 + s1^13*s2^4*s3^2 + s1^13*s2^4 + 
                    s1^13*s2^3*s3^4 + s1^13*s2^2*s3^2 + s1^13*s3^6 + s1^12*s2^12 + s1^12*s2^10 +
                    s1^12*s2^8*s3^2 + s1^12*s2^8*s3 + s1^12*s2^8 + s1^12*s2^7*s3 + s1^12*s2^7 + 
                    s1^12*s2^6*s3^2 + s1^12*s2^5*s3^3 + s1^12*s2^5*s3 + s1^12*s2^5 + 
                    s1^12*s2^4*s3^3 + s1^12*s2^4*s3 + s1^12*s2^4 + s1^12*s2^3*s3^2 + 
                    s1^12*s2^3*s3 + s1^12*s2^2*s3^5 + s1^12*s2^2*s3 + s1^12*s2*s3^5 + 
                    s1^12*s2*s3^2 + s1^12*s2*s3 + s1^12*s3^6 + s1^12*s3^4 + s1^11*s2^6*s3 + 
                    s1^11*s2^5 + s1^11*s2^4*s3^2 + s1^11*s2^3*s3^4 + s1^11*s2^3*s3 + s1^11*s2^3 +
                    s1^11*s2^2*s3^4 + s1^11*s2^2*s3^3 + s1^11*s2^2*s3^2 + s1^11*s2^2*s3 + 
                    s1^11*s2*s3^6 + s1^11*s2*s3^4 + s1^11*s3^6 + s1^11*s3^2 + s1^10*s2^8*s3^2 + 
                    s1^10*s2^7*s3 + s1^10*s2^6 + s1^10*s2^5*s3^2 + s1^10*s2^5*s3 + 
                    s1^10*s2^4*s3^4 + s1^10*s2^4*s3^2 + s1^10*s2^4*s3 + s1^10*s2^3*s3^5 + 
                    s1^10*s2^3*s3^3 + s1^10*s2^2*s3^5 + s1^10*s2^2*s3^4 + s1^10*s2^2*s3 + 
                    s1^10*s2*s3^5 + s1^10*s2*s3^3 + s1^10*s3^8 + s1^10*s3^7 + s1^10*s3^5 + 
                    s1^10*s3^3 + s1^9*s2^6*s3 + s1^9*s2^6 + s1^9*s2^5*s3 + s1^9*s2^4*s3^4 + 
                    s1^9*s2^4*s3^3 + s1^9*s2^4*s3^2 + s1^9*s2^4*s3 + s1^9*s2^4 + s1^9*s2^3*s3^2 + 
                    s1^9*s2^3*s3 + s1^9*s2^2*s3^4 + s1^9*s2*s3^6 + s1^9*s2*s3^4 + s1^9*s2*s3^3 + 
                    s1^9*s2*s3^2 + s1^9*s3^6 + s1^9*s3^5 + s1^8*s2^10*s3^2 + s1^8*s2^9*s3 + 
                    s1^8*s2^8*s3^4 + s1^8*s2^8*s3^2 + s1^8*s2^5*s3^3 + s1^8*s2^4*s3^2 + 
                    s1^8*s2^4*s3 + s1^8*s2^3*s3^5 + s1^8*s2^3*s3^4 + s1^8*s2^3*s3^3 + 
                    s1^8*s2^3*s3 + s1^8*s2^2*s3^6 + s1^8*s2^2*s3^3 + s1^8*s2*s3^7 + s1^8*s2*s3^4 + 
                    s1^8*s3^8 + s1^8*s3^7 + s1^8*s3^5 + s1^8*s3^4 + s1^8*s3^3 + s1^8*s3^2 + 
                    s1^7*s2^9*s3^2 + s1^7*s2^8*s3 + s1^7*s2^8 + s1^7*s2^7*s3^2 + s1^7*s2^6*s3^4 + 
                    s1^7*s2^6 + s1^7*s2^4*s3^4 + s1^7*s2^4*s3^3 + s1^7*s2^4*s3 + 
                    s1^7*s2^3*s3^2 + s1^7*s2^3*s3 + s1^7*s2^2*s3^5 + s1^7*s2*s3^2 + s1^7*s3^3 + 
                    s1^6*s2^11*s3 + s1^6*s2^10 + s1^6*s2^9*s3 + s1^6*s2^8*s3^3 + s1^6*s2^8 + 
                    s1^6*s2^7*s3^2 + s1^6*s2^7*s3 + s1^6*s2^6*s3^4 + s1^6*s2^6*s3^3 + 
                    s1^6*s2^6*s3^2 + s1^6*s2^6*s3 + s1^6*s2^6 + s1^6*s2^5*s3^3 + s1^6*s2^5 + 
                    s1^6*s2^4*s3^2 + s1^6*s2^4*s3 + s1^6*s2^3*s3^5 + s1^6*s2^3*s3^4 + 
                    s1^6*s2^3*s3^3 + s1^6*s2^3*s3^2 + s1^6*s2^3*s3 + s1^6*s2^2*s3^8 + 
                    s1^6*s2^2*s3^4 + s1^6*s2^2*s3^3 + s1^6*s2^2*s3^2 + s1^6*s2*s3^6 + s1^6*s3^6 + 
                    s1^6*s3^4 + s1^6*s3^3 + s1^5*s2^9 + s1^5*s2^7*s3^4 + s1^5*s2^6*s3^3 + 
                    s1^5*s2^6*s3^2 + s1^5*s2^6 + s1^5*s2^5*s3^4 + s1^5*s2^5*s3^2 + s1^5*s2^5 + 
                    s1^5*s2^4*s3^6 + s1^5*s2^4*s3^3 + s1^5*s2^3*s3^3 + s1^5*s2^2*s3^4 + 
                    s1^5*s2*s3^8 + s1^5*s2*s3^5 + s1^5*s2*s3^4 + s1^5*s3^8 + s1^5*s3^7 + 
                    s1^5*s3^6 + s1^4*s2^10 + s1^4*s2^9*s3^3 + s1^4*s2^8*s3^4 + s1^4*s2^8*s3^2 + 
                    s1^4*s2^8*s3 + s1^4*s2^8 + s1^4*s2^7*s3 + s1^4*s2^6*s3^5 + s1^4*s2^6*s3^2 + 
                    s1^4*s2^5*s3^5 + s1^4*s2^5*s3^4 + s1^4*s2^4*s3^8 + s1^4*s2^4*s3^6 + 
                    s1^4*s2^4*s3^5 + s1^4*s2^4*s3^4 + s1^4*s2^4*s3 + s1^4*s2^3*s3^5 + 
                    s1^4*s2^3*s3^3 + s1^4*s2^2*s3^8 + s1^4*s2*s3^7 + s1^4*s2*s3^6 + s1^4*s2*s3^5 +
                    s1^4*s3^10 + s1^4*s3^9 + s1^4*s3^8 + s1^4*s3^6 + s1^3*s2^9 + s1^3*s2^8 + 
                    s1^3*s2^7*s3^4 + s1^3*s2^7 + s1^3*s2^6*s3^3 + s1^3*s2^6 + s1^3*s2^5*s3^6 + 
                    s1^3*s2^5*s3^4 + s1^3*s2^5*s3 + s1^3*s2^4*s3^6 + s1^3*s2^4*s3^5 + 
                    s1^3*s2^3*s3^6 + s1^3*s2^3*s3^4 + s1^3*s2^3*s3^3 + s1^3*s2^3*s3^2 + 
                    s1^3*s2^2*s3^8 + s1^3*s2^2*s3^6 + s1^3*s2^2*s3^2 + s1^3*s2*s3^4 + s1^3*s3^8 +
                    s1^3*s3^5 + s1^3*s3^4 + s1^2*s2^12 + s1^2*s2^10*s3^2 + s1^2*s2^9*s3^3 + 
                    s1^2*s2^9*s3 + s1^2*s2^8*s3 + s1^2*s2^8 + s1^2*s2^7*s3^5 + s1^2*s2^7*s3^3 + 
                    s1^2*s2^7*s3 + s1^2*s2^7 + s1^2*s2^6*s3^5 + s1^2*s2^6*s3^4 + s1^2*s2^6*s3 + 
                    s1^2*s2^5*s3^5 + s1^2*s2^5*s3^4 + s1^2*s2^5*s3^3 + s1^2*s2^4*s3^7 + 
                    s1^2*s2^4*s3^5 + s1^2*s2^4*s3^4 + s1^2*s2^4*s3^3 + s1^2*s2^3*s3^6 + 
                    s1^2*s2^3*s3^5 + s1^2*s2^3*s3^3 + s1^2*s2^3*s3^2 + s1^2*s2^2*s3^7 + 
                    s1^2*s2^2*s3^6 + s1^2*s2*s3^5 + s1^2*s3^10 + s1^2*s3^6 + s1*s2^11 + 
                    s1*s2^7*s3^2 + s1*s2^7*s3 + s1*s2^7 + s1*s2^6*s3^2 + s1*s2^5*s3^6 + 
                    s1*s2^5*s3^4 + s1*s2^5*s3^2 + s1*s2^5*s3 + s1*s2^4*s3^5 + s1*s2^4*s3^3 + 
                    s1*s2^3*s3^8 + s1*s2^3*s3^3 + s1*s2^3*s3^2 + s1*s2^2*s3^8 + s1*s2^2*s3^7 + 
                    s1*s2^2*s3^4 + s1*s2^2*s3^3 + s1*s2*s3^8 + s1*s2*s3^5 + s1*s3^10 + s1*s3^8 +
                    s1*s3^7 + s1*s3^6 + s1*s3^4 + s2^14 + s2^12 + s2^10*s3^2 + s2^10*s3 + s2^10 +
                    s2^9 + s2^8*s3^4 + s2^8 + s2^7*s3^5 + s2^7*s3^3 + s2^7 + s2^6*s3^6 + 
                    s2^6*s3^4 + s2^6*s3^3 + s2^6*s3 + s2^5*s3^7 + s2^5*s3^5 + s2^5*s3^3 + 
                    s2^5*s3^2 + s2^4*s3^8 + s2^4*s3^7 + s2^4*s3^5 + s2^4*s3^4 + s2^4*s3^3 + 
                    s2^4*s3^2 + s2^3*s3^6 + s2^3*s3^3 + s2^2*s3^10 + s2^2*s3^9 + s2^2*s3^8 + 
                    s2^2*s3^5 + s2^2*s3^3 + s2*s3^8 + s2*s3^6 + s2*s3^5 + s2*s3^4 + s3^12 + 
                    s3^10 + s3^9 + s3^8 + s3^7 + s3^5 + s3^4;
                bool, s2 := HasRoot(F);
            until bool and s3 ne 0;
        else
            require false: "Argument 2 must be in {5,8,12,13,17,24} in characteristic 2.";
        end case;
        JJ :=  [ 1, ss^2, ss^4, ((s1^2*s3^4 + s2^8 + s2^6*s3)/s3^4)^2, s3^2 ] where ss := s2^2/s3;
    elif Characteristic(FF) eq 3 then
        /*
        Note that in the thesis of Gruenewald, s2, s3, s5, s6 are the Satake power sums,
        which I will denote p1 = 0, p2, p3, p4 = p2^2/4, p5, p6 here.  I reserve si for the 
        symmetric sums in this description.  Note that the power sums are not well-behaved
        in characteristics < 7.  Nevertheless, outside of this note, I use Gruenewald's
        notation for Satake power sums and conversions between invariants of Satake and Igusa.
        In particular, the Satake Humbert polynomials, computed by Gruenewald, are in terms
        of the Satake power sums.

        For discriminants D = 0 mod 4 we use the parametrization of the Satake sextic

            S(x) = x^6 + s2*x^4 - s3*x^3 + s4*x^2 - s5*x + s6,

        with s4 = s2^2/4 and S(x1) = S(x2) = 0, given by

            T(u) = u^6 - t1*u^5 + t2*u^4 - t3*u^3 + t4*u^2 - t5*u + t6,

        such that T(1) = T(-1) = 0, via the change of variables: 

            T(u) = S((x1-x2)*u/2+(x1+x2)/2) and S(x) = T((2*x-x1-x2)/(x1-x2)).

        This gives t1 = -6*(x1+x2)/(x1-x2) and t4, t5, and t6 are expressions in p1 = x1+x2, t1, t2, t3,
        in particular:

            t4 = (5*t1^4 - 24*t1^2*t2 + 32*t1*t3 + 16*t2^2)/64,
            t5 = -t1 - t3,
            t6 = - 1 - t2 - t4.

        The involution (x1,x2) -> (x2,x1) gives an involution (t1,t2,t3) -> (-t1,t2,-t3), and
        we descend to an expression in (t1^2,t2,t3/t1).

        The Satake power sums pi associated to S(x) are:

        [p2,p3,p5,p6] := [
             (15*t1^2 - 36*t2)/(2*t1^2),
             (-15*t1^3 + 54*t1*t2 - 81*t3)/(t1^3),
             (-4215*t1^5 + 27720*t1^3*t2 - 25920*t1^2*t3 - 45360*t1*t2^2 + 77760*t1 + 77760*t2*t3 + 77760*t3)/(64*t1^5),
             (2955*t1^6 - 22005*t1^4*t2 + 10935*t1^4 + 24624*t1^3*t3 + 44712*t1^2*t2^2 - 52488*t1^2*t2 -  23328*t1^2 -
             93312*t1*t2*t3 + 46656*t1*t3 - 11664*t2^3 + 34992*t2^2 + 139968*t2 + 69984*t3^2 + 139968)/(32*t1^6)
        ]

        up to (2,3,5,6)-weighted normalization by p1.  Hence (t1^2,t2,t1*t3) give an affine
        parametrization of the field of invariants, and the open patch t1 = 0 gives the locus
        with p-rank < 2.


        For discriminants D = 5 mod 8 we use the parametrization of the Satake sextic

            S(x) = x^6 + s2*x^4 - s3*x^3 + s4*x^2 - s5*x + s6,

        with s4 = s2^2/4 and S(x1) = 0, given by

            T(u) = u^6 - t1*u^5 + t2*u^4 - t3*u^3 + t4*u^2 - t5*u,

        via the change of variables

            S(x) = 6^6 * T((x-x1)/6) [or T(u) = S(6*x+x1)/6^6].

        The Satake power sums pi associated to S(x) are then:

        [p2,p3,p5,p6] := [
            30*t1^2 - 72*t2,
            120*t1^3 - 432*t1*t2 + 648*t3,
            (4215*t1^5 - 27720*t1^3*t2 + 25920*t1^2*t3 + 45360*t1*t2^2 - 77760*t2*t3 + 77760*t5)/2,
            5910*t1^6 - 44010*t1^4*t2 + 49248*t1^3*t3 + 89424*t1^2*t2^2 - 186624*t1*t2*t3 + 46656*t1*t5 - 23328*t2^3 + 139968*t3^2
        ]

        For D = 1 mod 8 there is work to be done (see the thesis of Gruenewald).

        */
        if D notin {5,8,12,13} then
            require false: "Not implemented for this discriminant.";
        end if;
        case D:
        when 5:
            /*
            Using the parametrization for D = 5 mod 8 in terms of (t1:t2:t3:t5)
            with defining equation t2 = 0: 
            */
            t1 := 1; // ordinary curves only
            t2 := 0; // defining equation F5 = 3*t1^2 - 8*t2 = 0
	    t3 := Random(FF);
	    t5 := Random(FF);
	    while t1^2*(t3 - t1^3) eq t5 do
                t5 := Random(FF);
	    end while;
            JJ := SatakeToIgusaInvariantsParametrization5Characteristic3([t1,t2,t3,t5]);
        when 8:
            /*
            Using the parametrization for D = 0 mod 4, first in terms of (t1,t2,t3):

                X8 = t1^2 - 4*t2 - 6

            then descending to (s2,t2,s4) = (t1^2,t2,t1*t3):

                F8 = s2 - 4*t2 - 6

            Note that there are two extraneous components:

                // First extraneous component:
                F8 := s2^6 + s2^5*t2 + 2*s2^5 + s2^4*t2 + s2^4*s4 + s2^4 + s2^3*t2^3 + 2*s2^3*t2*s4 + s2^3*s4 +
                    2*s2^2*t2^3 + s2^2*t2^2*s4 + s2^2*s4^2 + s2*t2^5 + s2*t2^4 + 2*t2^6;
                // Second extraneous component:
                F8 := s2^8 + s2^6*t2^2 + s2^5*t2^3 + s2^5*t2^2 + s2^5*t2*s4 + s2^5*s4 - s2^5
                    - s2^4*t2^3 + s2^4*t2^2 + s2^4*t2*s4 - s2^4*s4 - s2^3*t2^5 + s2^3*t2^4 
                    - s2^3*t2^3*s4 - s2^3*t2^3 - s2^3*s4^2 - s2^2*t2^6 + s2^2*t2^5 - s2^2*t2^4*s4 
                    + s2^2*t2^4 + s2^2*t2^2*s4^2 + s2*t2^7 + s2*t2^6 + s2*t2^5*s4 + t2^8;

            which give covers of higher level corresponding to certain extra factorizations
            of the Satake sextic (beyond its quadratic and quartic factors).
            */
            s2 := Random(FF);
	    while s2 eq 0 do
		s2 := Random(FF);
	    end while;
	    t2 := s2; // s2 = 4*t2 + 6 in char 0
            s4 := Random(FF);
	    while s2 eq -s4 do
		s4 := Random(FF);
	    end while;
            JJ := SatakeToIgusaInvariantsParametrization0Characteristic3([s2,t2,s4]);
            if JJ[5] eq 0 then print [s2,t2,s4]; assert false; end if; 
        when 12:
            /*
            Using the parametrization for D = 0 mod 4, in terms of (t1,t2,t3):

                X12 = 5*t1^4 - 24*t1^2*t2 + 20*t1^2 + 32*t1*t3 + 16*t2^2 + 48*t2 + 36

            we obtain the parametrization in terms of (s2=t1^2,t2,s4=t1*t3):

                F12 = 5*s2^2 - 24*s2*t2 + 20*s2 + 32*s4 + 16*t2^2 + 48*t2 + 36

            in characteristic 3, this is s2^2 + s2 + 2*t2^2 + s4.
            */
            bool := false;
	    s2 := Random(FF);
	    while s2 eq 0 do
		s2 := Random(FF);
	    end while;
	    t2 := Random(FF);
	    while t2 eq s2 + 1 or t2 eq s2 do
		t2 := Random(FF);
	    end while;
	    s4 := t2^2 - s2*(s2 + 1);
            JJ := SatakeToIgusaInvariantsParametrization0Characteristic3([s2,t2,s4]);
        when 13:
            t1 := 1; // ordinary curves only
            repeat
                t2 := Random(FF);
                t3 := Random(FF);
                t5 := PolynomialRing(FF).1;
		F13 := t2^5 + t2^4 + t2^3*(t3+1) - t2^2*(t5+1) + t2*(t3^2-t3*t5-1) + (t3-t5-1)*t5;
                bool, t5 := HasRoot(F13);
	    until bool and t2^2 + t2*t3 + t2 + 2*t3 + t5 + 1 ne 0;
            JJ := SatakeToIgusaInvariantsParametrization5Characteristic3([t1,t2,t3,t5]);
        when 17:
            require false : "Not implemented.";
        when 21:
            require false : "Not implemented.";
        else
            require false: "Not implemented for this discriminant.";
        end case;
    elif Characteristic(FF) eq 5 then
        if D notin {5,8,12,13} then
            require false: "Not implemented for this discriminant.";
        end if;
	case D:
        when 5:
            /*
            Using the parametrization for D = 5 mod 8 in terms of (t1:t2:t3:t5)
            with defining equation t2 = 0:
            */
            t1 := Random(FF);
            t2 := t1^2; // defining equation F5 = 3*t1^2 - 8*t2 = 0
	    t3 := Random(FF);
	    t5 := Random(FF);
	    while (t1^2 + t2)*(t1^3 + t1*t2 + 3*t3) eq t5 do
                t5 := Random(FF);
	    end while;
            JJ := SatakeToIgusaInvariantsParametrization5Characteristic5([t1,t2,t3,t5]);
            if JJ[5] eq 0 then print [s2,t2,s4]; assert false; end if;
        when 8:
            /*
            Using the parametrization for D = 0 mod 4, first in terms of (t1,t2,t3):

                X8 = t1^2 - 4*t2 - 6,

            then descending to (s2,t2,s4) = (t1^2,t2,t1*t3):

                F8 = s2 - 4*t2 - 6.
            */
            s2 := Random(FF);
	    while s2 eq 0 do
		s2 := Random(FF);
	    end while;
	    t2 := -(s2-1); // s2 = 4*t2 + 6 in char 0
            s4 := Random(FF);
	    while s4 eq 3*(s2*(s2 + t2 + 3)) do
		s4 := Random(FF);
	    end while;
	    JJ := SatakeToIgusaInvariantsParametrization0Characteristic5([s2,t2,s4]);
            if JJ[5] eq 0 then print [s2,t2,s4]; assert false; end if;
	when 12:
            /*
            Using the parametrization for D = 0 mod 4, in terms of (t1,t2,t3):

                X12 = 5*t1^4 - 24*t1^2*t2 + 20*t1^2 + 32*t1*t3 + 16*t2^2 + 48*t2 + 36

            we obtain the parametrization in terms of (s2=t1^2,t2,s4=t1*t3):

                F12 = 5*s2^2 - 24*s2*t2 + 20*s2 + 32*s4 + 16*t2^2 + 48*t2 + 36

            in characteristic 5, this is s2*t2 + 2*s4 + t2^2 + 3*t2 + 1.
            */
            bool := false;
	    s2 := Random(FF);
	    while s2 eq 0 do
		s2 := Random(FF);
	    end while;
	    repeat
		t2 := Random(FF);
	    until s2+t2 notin {FF|1,3};
	    s4 := 2*(s2*t2 + t2^2 + 3*t2 + 1);
            JJ := SatakeToIgusaInvariantsParametrization0Characteristic5([s2,t2,s4]);
            if JJ[5] eq 0 then print [s2,t2,s4]; assert false; end if;
        when 13:
            repeat
		t1 := Random(FF);
                t2 := Random(FF);
                t3 := Random(FF);
                t5 := PolynomialRing(FF).1;
		F13 := t1^6*t2^2 - t1^5*t2*t3 - t1^4*t3^2 + 2*t1^3*t2^2*t3 + 3*t1^3*t2*t5 - t1^2*t2*t3^2
		    + t1^2*t3*t5 - t1*t2^3*t3 + 3*t1*t2^2*t5 - t2^5 + 2*t2^2*t3^2 + 3*t2*t3*t5 + t5^2;
                bool, t5 := HasRoot(F13);
	    until bool and (t1^2 + t2)*(t1^3 + t1*t2 + 3*t3) ne t5;
            JJ := SatakeToIgusaInvariantsParametrization5Characteristic5([t1,t2,t3,t5]);
            if JJ[5] eq 0 then print [t1,t2,t3,t5]; assert false; end if;
	end case;
    else
        if D notin {4,5,8,9,12,13,16,17,20,21} then
            require false: "Not implemented for this discriminant.";
        end if;
        HD := Level1SatakeHumbertPolynomial(FF,D);
        repeat
            s2 := Random(FF);
            s3 := Random(FF);
            s5 := Random(FF);
            s6 := PolynomialRing(FF).1;
            FD := Evaluate(HD,[s2,s3,s5,s6]);
	    bool, s6 := HasRoot(FD);
        until bool and 5*s2*s3 ne 12*s5;
        JJ := SatakeToIgusaInvariants([s2,s3,s5,s6]);
    end if;
    if AbsolutelySimple then
        require not IsSquare(D): "Jacobian can not be absolutely simple with square discriminant.";
	C := HyperellipticCurveFromIgusaInvariants(JJ);
        chi := FrobeniusCharacteristicPolynomial(C);
        if not IsIrreducible(chi) or QuarticCMFieldType(NumberField(chi)) eq [2,2] then
            return RandomIgusaInvariantsWithRM(FF,D : AbsolutelySimple := true);
        end if;
    end if;
    return JJ;
end intrinsic;
