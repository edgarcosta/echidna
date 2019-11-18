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

function RosenhainHumbertPolynomial05Evaluated(ee)
    assert #ee eq 3;
    e1,e2,e3 := Explode(ee);
    return 
	e1^4*e2^2*e3^2 - 2*e1^4*e2*e3^2 + e1^4*e3^2 - 2*e1^3*e2^3*e3^2 + 
	2*e1^3*e2^3*e3 - 2*e1^3*e2^2*e3^2 + 2*e1^3*e2*e3^3 + 4*e1^3*e2*e3^2 - 
	2*e1^3*e2*e3 - 2*e1^3*e3^3 + e1^2*e2^4*e3^2 - 2*e1^2*e2^4*e3 + e1^2*e2^4
	+ 4*e1^2*e2^3*e3^2 - 2*e1^2*e2^3*e3 - 2*e1^2*e2^3 - 4*e1^2*e2^2*e3^2 + 
	4*e1^2*e2^2*e3 + e1^2*e2^2 - 2*e1^2*e2*e3^3 + e1^2*e3^4 - 2*e1*e2^3*e3^3
	+ 2*e1*e2^3*e3 + 4*e1*e2^2*e3^3 - 2*e1*e2^2*e3^2 - 2*e1*e2^2*e3 - 
	2*e1*e2*e3^4 + 2*e1*e2*e3^3 + e2^2*e3^4 - 2*e2^2*e3^3 + e2^2*e3^2;
end function;

function RosenhainHumbertPolynomials05Evaluated(ee)
    assert #ee eq 3;
    e1,e2,e3 := Explode(ee);
    /* 6 components: */
    return {@
	e1^4*e2^2*e3^2 - 2*e1^4*e2*e3^2 + e1^4*e3^2 - 2*e1^3*e2^3*e3^2 + 
	2*e1^3*e2^3*e3 - 2*e1^3*e2^2*e3^2 + 2*e1^3*e2*e3^3 + 4*e1^3*e2*e3^2 - 
	2*e1^3*e2*e3 - 2*e1^3*e3^3 + e1^2*e2^4*e3^2 - 2*e1^2*e2^4*e3 + e1^2*e2^4
	+ 4*e1^2*e2^3*e3^2 - 2*e1^2*e2^3*e3 - 2*e1^2*e2^3 - 4*e1^2*e2^2*e3^2 + 
	4*e1^2*e2^2*e3 + e1^2*e2^2 - 2*e1^2*e2*e3^3 + e1^2*e3^4 - 2*e1*e2^3*e3^3
	+ 2*e1*e2^3*e3 + 4*e1*e2^2*e3^3 - 2*e1*e2^2*e3^2 - 2*e1*e2^2*e3 - 
	2*e1*e2*e3^4 + 2*e1*e2*e3^3 + e2^2*e3^4 - 2*e2^2*e3^3 + e2^2*e3^2,
	e1^4*e2^2*e3^2 - 2*e1^4*e2^2*e3 + e1^4*e2^2 - 2*e1^3*e2^3*e3^2 + 
	2*e1^3*e2^3*e3 + 4*e1^3*e2^2*e3^2 - 2*e1^3*e2^2*e3 - 2*e1^3*e2^2 - 
	2*e1^3*e2*e3^3 + 2*e1^3*e2*e3 + e1^2*e2^4*e3^2 - 2*e1^2*e2^3*e3^2 - 
	4*e1^2*e2^2*e3^2 + 4*e1^2*e2^2*e3 + e1^2*e2^2 + 4*e1^2*e2*e3^3 - 
	2*e1^2*e2*e3^2 - 2*e1^2*e2*e3 + e1^2*e3^4 - 2*e1^2*e3^3 + e1^2*e3^2 - 
	2*e1*e2^4*e3^2 + 2*e1*e2^3*e3^3 + 4*e1*e2^3*e3^2 - 2*e1*e2^3*e3 - 
	2*e1*e2^2*e3^3 - 2*e1*e2*e3^4 + 2*e1*e2*e3^3 + e2^4*e3^2 - 2*e2^3*e3^3 +
	e2^2*e3^4,
	e1^4*e2^2*e3^2 - 2*e1^4*e2*e3^2 + e1^4*e3^2 - 2*e1^3*e2^3*e3 - 
	2*e1^3*e2^2*e3^3 + 4*e1^3*e2^2*e3^2 + 2*e1^3*e2*e3^3 - 2*e1^3*e2*e3^2 + 
	2*e1^3*e2*e3 - 2*e1^3*e3^2 + e1^2*e2^4 + 4*e1^2*e2^3*e3 - 2*e1^2*e2^3 + 
	e1^2*e2^2*e3^4 - 2*e1^2*e2^2*e3^3 - 4*e1^2*e2^2*e3^2 - 2*e1^2*e2^2*e3 + 
	e1^2*e2^2 + 4*e1^2*e2*e3^2 - 2*e1^2*e2*e3 + e1^2*e3^2 - 2*e1*e2^4*e3 + 
	2*e1*e2^3*e3^3 - 2*e1*e2^3*e3^2 + 2*e1*e2^3*e3 - 2*e1*e2^2*e3^4 + 
	4*e1*e2^2*e3^3 - 2*e1*e2*e3^3 + e2^4*e3^2 - 2*e2^3*e3^3 + e2^2*e3^4,
	e1^4*e2^2*e3^2 - 2*e1^4*e2^2*e3 + e1^4*e2^2 + 2*e1^3*e2^3*e3 - 2*e1^3*e2^3 -
	2*e1^3*e2^2*e3^3 - 2*e1^3*e2^2*e3^2 + 4*e1^3*e2^2*e3 + 2*e1^3*e2*e3^3 - 
	2*e1^3*e2*e3 + e1^2*e2^4 - 2*e1^2*e2^3*e3 + e1^2*e2^2*e3^4 + 
	4*e1^2*e2^2*e3^3 - 4*e1^2*e2^2*e3^2 - 2*e1^2*e2*e3^4 - 2*e1^2*e2*e3^3 + 
	4*e1^2*e2*e3^2 + e1^2*e3^4 - 2*e1^2*e3^3 + e1^2*e3^2 - 2*e1*e2^4*e3 - 
	2*e1*e2^3*e3^3 + 4*e1*e2^3*e3^2 + 2*e1*e2^3*e3 - 2*e1*e2^2*e3^2 + 
	2*e1*e2*e3^3 - 2*e1*e2*e3^2 + e2^4*e3^2 - 2*e2^3*e3^2 + e2^2*e3^2,
	e1^4*e2^2 - 2*e1^4*e2*e3 + e1^4*e3^2 - 2*e1^3*e2^3*e3 + 4*e1^3*e2^2*e3 - 
	2*e1^3*e2^2 + 2*e1^3*e2*e3^3 - 2*e1^3*e2*e3^2 + 2*e1^3*e2*e3 - 
	2*e1^3*e3^3 + e1^2*e2^4*e3^2 - 2*e1^2*e2^3*e3^3 + 4*e1^2*e2^3*e3^2 + 
	e1^2*e2^2*e3^4 - 2*e1^2*e2^2*e3^3 - 4*e1^2*e2^2*e3^2 - 2*e1^2*e2^2*e3 + 
	e1^2*e2^2 - 2*e1^2*e2*e3^4 + 4*e1^2*e2*e3^3 + e1^2*e3^4 - 2*e1*e2^4*e3^2
	+ 2*e1*e2^3*e3^3 - 2*e1*e2^3*e3^2 + 2*e1*e2^3*e3 + 4*e1*e2^2*e3^2 - 
	2*e1*e2^2*e3 - 2*e1*e2*e3^3 + e2^4*e3^2 - 2*e2^3*e3^2 + e2^2*e3^2,
	e1^4*e2^2 - 2*e1^4*e2*e3 + e1^4*e3^2 + 2*e1^3*e2^3*e3 - 2*e1^3*e2^3 - 
	2*e1^3*e2^2*e3 - 2*e1^3*e2*e3^3 + 4*e1^3*e2*e3^2 + 2*e1^3*e2*e3 - 
	2*e1^3*e3^2 + e1^2*e2^4*e3^2 - 2*e1^2*e2^4*e3 + e1^2*e2^4 - 
	2*e1^2*e2^3*e3^3 - 2*e1^2*e2^3*e3^2 + 4*e1^2*e2^3*e3 + e1^2*e2^2*e3^4 + 
	4*e1^2*e2^2*e3^3 - 4*e1^2*e2^2*e3^2 - 2*e1^2*e2*e3^2 + e1^2*e3^2 + 
	2*e1*e2^3*e3^3 - 2*e1*e2^3*e3 - 2*e1*e2^2*e3^4 - 2*e1*e2^2*e3^3 + 
	4*e1*e2^2*e3^2 + 2*e1*e2*e3^3 - 2*e1*e2*e3^2 + e2^2*e3^4 - 2*e2^2*e3^3 +
	e2^2*e3^2
	@};
end function;

function RosenhainHumbertPolynomial05(R)
    P<e1,e2,e3> := PolynomialRing(R, 3 : Global);
    return RosenhainHumbertPolynomial05Evaluated([e1,e2,e3]);
end function;

function RosenhainHumbertPolynomials05(R)
    P<e1,e2,e3> := PolynomialRing(R, 3 : Global);
    return RosenhainHumbertPolynomials05Evaluated([e1,e2,e3]);
end function;
