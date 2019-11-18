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

function Level2ThetaNullHumbertPolynomials16(R)
    P<a00,a02,a20,a22> := PolynomialRing(R, 4 : Global);
    //print "Warning: returning only one component.";
    return {@
        16*a00^4*a20^2*a22^2 - 8*a00^3*a02*a20^4 - 48*a00^3*a02*a20^2*a22^2 -
        8*a00^3*a02*a22^4 + 16*a00^2*a02^2*a20^4 + 64*a00^2*a02^2*a20^2*a22^2 +
	16*a00^2*a02^2*a22^4 - 8*a00*a02^3*a20^4 - 48*a00*a02^3*a20^2*a22^2 -
	8*a00*a02^3*a22^4 + 16*a02^4*a20^2*a22^2 + a20^8 - 4*a20^6*a22^2 +
	6*a20^4*a22^4 - 4*a20^2*a22^6 + a22^8
        @};
end function;
