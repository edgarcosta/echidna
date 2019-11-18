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

function RosenhainHumbertPolynomial04Evaluated(ee)
    assert #ee eq 3;
    e1,e2,e3 := Explode(ee);
    return e1*e2 - e3;
end function;

function RosenhainHumbertPolynomials04Evaluated(ee)
    assert #ee eq 3;
    e1,e2,e3 := Explode(ee);
    /* 15 components: */
    return {@
	e1*e2 - e3,
	e1*e3 - e2,
	e1 - e2*e3,
	e1*e2 - e1*e3 + e2*e3 - e2,
	e1*e2 - e1*e3 - e1 + e3,
	e1*e2 - e1 - e2*e3 + e2,
	e1*e2 - e1*e3 - e2*e3 + e3,
	e1*e3 - e2*e3 + e2 - e3,
	e1*e2 - e2*e3 - e2 + e3,
	e1 + e2*e3 - e2 - e3,
	e1*e2 + e1*e3 - e1 - e2*e3,
	e1*e3 - e1 + e2 - e3,
	e1*e2 - e1 - e2 + e3,
	e1*e2 - e1*e3 + e1 - e2,
	e1*e3 - e1 - e2*e3 + e3
	@};
end function;


function RosenhainHumbertPolynomial04(R)
    P<e1,e2,e3> := PolynomialRing(R, 3 : Global);
    return RosenhainHumbertPolynomial04Evaluated([e1,e2,e3]);
end function;

function RosenhainHumbertPolynomials04(R)
    P<e1,e2,e3> := PolynomialRing(R, 3 : Global);
    return RosenhainHumbertPolynomials04Evaluated([e1,e2,e3]);
end function;
