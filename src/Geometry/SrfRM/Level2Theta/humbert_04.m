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

function Level2ThetaNullHumbertPolynomials04(R)
    P<a00,a02,a20,a22> := PolynomialRing(R, 4 : Global);
    return {@
	a00,
	a02,
	a20,
	a22,
	a00 - a22,
	a00 - a02,
	a00 - a20,
	a02 - a22,
	a20 - a22,
	a02 - a20,
	a00 + a02,
	a00 + a20,
	a00 + a22,
	a02 + a20,
	a02 + a22,
	a20 + a22,
	a00 + a02 + a20 + a22,
	a00 + a02 + a20 - a22,
	a00 + a02 - a20 + a22,
	a00 + a02 - a20 - a22,
	a00 - a02 + a20 - a22,
	a00 - a02 + a20 + a22,
	a00 - a02 - a20 - a22,
	a00 - a02 - a20 + a22,
	a00^2 + a02^2,
	a00^2 + a20^2,
	a00^2 + a22^2,
	a02^2 + a20^2,
	a02^2 + a22^2,
	a20^2 + a22^2,
	a00^2 + 2*a00*a20 + a02^2 + 2*a02*a22 + a20^2 + a22^2,
	a00^2 + 2*a00*a22 + a02^2 + 2*a02*a20 + a20^2 + a22^2,
	a00^2 + 2*a00*a02 + a02^2 + a20^2 + 2*a20*a22 + a22^2,
	a00^2 + 2*a00*a22 + a02^2 - 2*a02*a20 + a20^2 + a22^2,
	a00^2 + 2*a00*a20 + a02^2 - 2*a02*a22 + a20^2 + a22^2,
	a00^2 + 2*a00*a02 + a02^2 + a20^2 - 2*a20*a22 + a22^2,
	a00^2 - 2*a00*a22 + a02^2 - 2*a02*a20 + a20^2 + a22^2,
	a00^2 - 2*a00*a02 + a02^2 + a20^2 - 2*a20*a22 + a22^2,
	a00^2 - 2*a00*a20 + a02^2 - 2*a02*a22 + a20^2 + a22^2,
	a00^2 - 2*a00*a22 + a02^2 + 2*a02*a20 + a20^2 + a22^2,
	a00^2 - 2*a00*a20 + a02^2 + 2*a02*a22 + a20^2 + a22^2,
	a00^2 - 2*a00*a02 + a02^2 + a20^2 + 2*a20*a22 + a22^2
	@};
end function;
