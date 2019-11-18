//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Enumeration of moduli points over small finite fields.                  //
//                                                                          //
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu.au>                //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*

N.B. If C is a supersingular genus 2 curve, then its Igusa invariants
are of the form [ J2 : J4 : J6 : J8: J10] = [ 0 : 0 : A : 0 : B ].
Such a curve has model y^2 = f(x) where f(x) = x^6 + A*x^3 + B*x + A^2.

The condition J2 = 0 appears to be equivalent to C having p-rank < 2;
such a curve has model y^2 = f(x) + g(x) where deg(g) < 4 and f(x) is
as above.

In terms of a model y^2 = x*(x-e0)*(x-e1)*(x-e2)*(x-e3), we have the
following condition:

      J2 = e0^2*(e1*e2 + e1*e3 + e2*e3) +
           e1^2*(e0*e2 + e0*e3 + e2*e3) + 
           e2^2*(e0*e1 + e1*e3 + e0*e3) + 
           e3^2*(e0*e2 + e0*e1 + e1*e2) = 0.

*/

function J2FromRosenhain(ee)
    e0 := Universe(ee)!1;
    e1, e2, e3 := Explode(ee); 
    return
	e0^2*(e1*e2 + e1*e3 + e2*e3) +
	e1^2*(e0*e2 + e0*e3 + e2*e3) + 
	e2^2*(e0*e1 + e1*e3 + e0*e3) + 
	e3^2*(e0*e2 + e0*e1 + e1*e2);
end function;

function IsAbsolutelySimple(ee)
    // This only excludes Jacobians which are (2,2)-split.
    e1, e2, e3 := Explode(ee); 
    if e1*e2 eq e3 or e1*e3 eq e2 or e2*e3 eq e1 then
	return false;
    end if;
    ALL_2Split := {
        e1 - e2*e3,
	e1*e2 - e1*e3 + e2*e3 - e2,
	e1*e2 - e1*e3 - e1 + e3,
	e1*e2 - e2*e3 - e2 + e3,
	e1*e2 - e1*e3 - e2*e3 + e3,
	e1*e3 - e2*e3 + e2 - e3,
	e1 + e2*e3 - e2 - e3,
	e1*e2 - e1*e3 + e1 - e2,
	e1*e2 - e1 - e2 + e3,
	e1*e3 - e1 - e2*e3 + e3,
	e1*e3 - e1 + e2 - e3,
	e1*e2 - e1 - e2*e3 + e2,
	e1*e2 - e3,
	e1*e3 - e2,
	e1*e2 + e1*e3 - e1 - e2*e3
	};
    return 0 notin ALL_2Split;
end function;

/////////////////////////////////////////////////////////////////////////
// Some functions for enumeration of Rosenhain and Thomae constants.
/////////////////////////////////////////////////////////////////////////

intrinsic RosenhainRMLocus(D::RngIntElt,ee::SeqEnum[RngElt])
    -> FldFinElt
    {}
    require D in {4,5,8} : "Argument 1 must be 4, 5 or 8.";
    e1, e2, e3 := Explode(ee);
    // Hashimoto and Muribashi's equations:
    if D eq 4 then
	return e1*e2 - e3;
    elif D eq 5 then
	return 4*(e1^2*e3 - e2^2 + e3^2*(1-e1) + e2 - e3)*(e1^2*e2*e3
	    - e1*e2^2*e3) - (e1^2*(e2+1)*e3 - e2^2*(e1+e3)
	    + (1-e1)*e2*e3^2 + e1*(e2-e3))^2;
    elif D eq 8 then
	return 4*e1*e2*e3*((e1+e3)*(e2+1) - 2*(e1*e3+e2))^2
	    - (e2-1)^2*(e1-e3)^2*(e1*e3+e2)^2;
    end if;
end intrinsic;

intrinsic EnumerateOrdinaryRosenhainInvariantsWithRM(D::RngIntElt,FF::FldFin :
    ExcludeSplit := false) -> SeqEnum
    {}
    require D in {4,5,8} : "Argument 1 must be 4, 5 or 8.";
    // This ordinary condition applies only in char 3.
    p := Characteristic(FF);
    require p mod 2 eq 1 : "Argument 2 must have odd characteristic.";
    invs := [];
    x := PolynomialRing(FF).1; 
    for e1, e2 in FF do
	if e1 in {FF|0,1} or e2 in {FF|0,1} or e1 eq e2 then
	    continue;
	end if;
	e0 := FF!1;
	fD := RosenhainRMLocus(D,[e1,e2,x]);
	for rr in Roots(fD) do
	    e3 := rr[1];
	    ee := [e1,e2,e3];
	    if #{0,e0,e1,e2,e3} eq 5 and
		(p gt 3 or J2FromRosenhain(ee) ne 0) and 
		(not ExcludeSplit or IsAbsolutelySimple(ee)) then
		Append(~invs,ee);
	    end if;
	end for;
    end for;
    return invs;
end intrinsic;

intrinsic EnumerateOrdinaryRosenhainInvariants(FF::FldFin) -> SeqEnum
    {}
    // This ordinary condition applies only in char 2 or 3.
    // assert Characteristic(FF) in {2,3};
    p := Characteristic(FF);
    invs := [];
    for e1, e2, e3 in FF do
	e0 := FF!1;
	ee := [e1,e2,e3];
	if #{0,e0,e1,e2,e3} eq 5 then
	    if p gt 3 or J2FromRosenhain(ee) ne 0 then
		Append(~invs,ee);
	    end if;
	end if;
    end for;
    return invs;
end intrinsic;

intrinsic EnumerateOrdinaryLevel2ThetaNullPoints(FF::FldFin) -> SeqEnum
    {}
    // INPUT: A finite field of characteristic different from 2.
    // OUTPUT: The Thomae constants defined over the base field.
    ros_invs := EnumerateOrdinaryRosenhainInvariants(FF);
    thm_invs := [ ];
    ros_good := [ ];
    for ee in ros_invs do
	bool, tt := ExistsLevel2ThetaNullPointFromRosenhainInvariants(ee);
	if bool then
	    Append(~thm_invs,tt);
	    Append(~ros_good,ee);
	end if;
    end for;
    return thm_invs, ros_good;
end intrinsic;

