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

function RosenhainHumbertPolynomial01Evaluated(ee)
    assert #ee eq 3;
    e1,e2,e3 := Explode(ee);
    return e1;
end function;

function RosenhainHumbertPolynomials01Evaluated(ee)
    assert #ee eq 3;
    e1,e2,e3 := Explode(ee);
    /* 10 components (1 = component at infinity): */
    return {@
        e1,
        e2,
        e3,
        1 - e1,
        1 - e2,
        1 - e3,
        e1 - e2,
        e1 - e3,
        e2 - e3,
        1
	@};
end function;

function RosenhainHumbertPolynomial01(R)
    P<e1,e2,e3> := PolynomialRing(R, 3 : Global);
    return RosenhainHumbertPolynomial01Evaluated([e1,e2,e3]);
end function;

function RosenhainHumbertPolynomials01(R)
    P<e1,e2,e3> := PolynomialRing(R, 3 : Global);
    return RosenhainHumbertPolynomials01Evaluated([e1,e2,e3]);
end function;
