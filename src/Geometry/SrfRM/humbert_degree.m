//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2014 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
// See Runge, Endomorphism rings of abelian surfaces..., p.10-11            //
//////////////////////////////////////////////////////////////////////////////

function a1_D(D)
    xmax := Isqrt(D);
    if IsSquare(D) then
	xmax -:= 2;
    elif (D-xmax) mod 2 ne 0 then
	xmax -:= 1;
    end if;
    aD := IsSquare(D) select 12*D - 2 else 0;
    aD +:= 24*&+[ Integers() | &+Divisors((D-x^2) div 4) : x in [-xmax..xmax by 2] ]; 
    return aD;
end function;

function v1_D(D)
    return D mod 4 in {2,3} select 0 else D in {1,4} select 1/2 else 1;
end function;

function v2_D_rosenhain(D)
    return D mod 4 in {2,3} select 0 else 1;
end function;

function v2_D_theta(D)
    return D mod 4 in {2,3} select 0 else D eq 1 select 1/2 else 1;
end function;

function m2_D_rosenhain(D)
    // The number of components of the level 2 (Rosenhain) Humbert surface.
    /* This looks rather questionable, when D = 4^n D0 where D0 = 1 mod 4. */
    return D mod 4 eq 0 select 15 else D mod 8 eq 1 select 10 else 6;
end function;

function m2_D_theta(D)
    // The number of components of the level 2 theta null Humbert surface.
    /* This looks questionable when D = 4^n D0, where D0 = 1 mod 4. */
    return D mod 4 eq 0 select 60 else D mod 8 eq 1 select 10 else 6;
end function;

intrinsic DegreeOfLevel1HumbertPolynomial(D::RngIntElt) -> RngIntElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
        "Argument must be a positive discriminant.";
    ZZ := IntegerRing();
    D0 := IsSquare(D) select 1 else FundamentalDiscriminant(D);
    m0 := Isqrt(D div D0);
    degD := ZZ!(a1_D(D)/2);
    for D1 in [ m1^2*D0 : m1 in Divisors(m0) | m1 ne m0 ] do
        degD -:= v1_D(D1)*DegreeOfLevel1HumbertPolynomial(D1);
    end for;
    return ZZ!(degD/v1_D(D));
end intrinsic;

intrinsic DegreeOfRosenhainHumbertPolynomial(D::RngIntElt) -> RngIntElt
    {Attention: This is an conjectural formula from David Gruenewald's
    thesis; for square D = m^2, we scale by a correcting fudge factor
    (m-1)/m [coming from the missing component at oo?].}
    require D mod 4 in {0,1} and D gt 1 :
	"Argument must be a positive discriminant greater than 1.";
    ZZ := IntegerRing();
    if D eq 1 then return 1; end if;
    D0 := IsSquare(D) select 1 else FundamentalDiscriminant(D);
    m0 := Isqrt(D div D0);
    if D0 eq 1 then
        return ZZ!((m0-1)/m0*DegreeOfLevel2HumbertPolynomial(D));
    else
        return 4*DegreeOfLevel2HumbertPolynomial(D);
    end if;
end intrinsic;

intrinsic DegreeOfLevel2HumbertPolynomial(D::RngIntElt) -> RngIntElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument must be a positive discriminant greater than 0.";
    ZZ := IntegerRing();
    if D eq 1 then return 1; end if;
    D0 := IsSquare(D) select 1 else FundamentalDiscriminant(D);
    m0 := Isqrt(D div D0);
    degD := a1_D(D);
    for D1 in [ m1^2*D0 : m1 in Divisors(m0) | m1 lt m0 ] do
        degD +:= -m2_D_rosenhain(D1)*DegreeOfLevel2HumbertPolynomial(D1);
    end for;
    // Maybe the can be expressed more cleanly with a v2_D?
    if D0 ne 1 then degD *:= 1/4; end if;
    return ZZ!(degD/m2_D_rosenhain(D));
end intrinsic;

intrinsic DegreeOfLevel2ThetaNullHumbertPolynomial(D::RngIntElt) -> RngIntElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument must be a positive discriminant.";
    ZZ := IntegerRing();
    if D eq 1 or IsFundamental(D) then
	return ZZ!(a1_D(D)/(v2_D_theta(D)*m2_D_theta(D)));
    end if;
    D0 := IsSquare(D) select 1 else FundamentalDiscriminant(D);
    m0 := Isqrt(D div D0);
    degD := a1_D(D);
    for D1 in [ m1^2*D0 : m1 in Divisors(m0) | m1 ne m0 ] do
        deg1 := DegreeOfLevel2ThetaNullHumbertPolynomial(D1);
        degD +:= -v2_D_theta(D1)*m2_D_theta(D1)*deg1;
    end for;
    return ZZ!(degD/(v2_D_theta(D)*m2_D_theta(D)));
end intrinsic;

intrinsic NumberOfRosenhainHumbertComponents(D) -> RngIntElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument must be a positive discriminant > 1.";
    return m2_D_rosenhain(D);
end intrinsic;

intrinsic NumberOfLevel2HumbertComponents(D) -> RngIntElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument must be a positive discriminant > 1.";
    return m2_D_theta(D);
end intrinsic;

intrinsic NumberOfLevel2ThetaNullHumbertComponents(D) -> RngIntElt
    {}
    require D mod 4 in {0,1} and D gt 0 :
	"Argument must be a positive discriminant.";
    return m2_D_theta(D);
end intrinsic;

