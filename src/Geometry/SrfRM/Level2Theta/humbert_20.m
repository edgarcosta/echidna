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

function Level2ThetaNullHumbertPolynomials20(R)
    P<a00,a02,a20,a22> := PolynomialRing(R, 4 : Global);
    //print "Warning, returning only one component.";
    return {@
	64*a00^6*a22^2 - 16*a00^4*a02^3*a20 - 32*a00^4*a02^2*a20^2 - 16*a00^4*a02*a20^3 +
	128*a00^4*a22^4 - 32*a00^2*a02^4*a22^2 - 96*a00^2*a02^3*a20*a22^2 -
	128*a00^2*a02^2*a20^2*a22^2 - 96*a00^2*a02*a20^3*a22^2 - 32*a00^2*a20^4*a22^2 +
	64*a00^2*a22^6 + a02^8 + 8*a02^7*a20 + 28*a02^6*a20^2 + 56*a02^5*a20^3 + 70*a02^4*a20^4 + 
	56*a02^3*a20^5 - 16*a02^3*a20*a22^4 + 28*a02^2*a20^6 - 32*a02^2*a20^2*a22^4 +
	8*a02*a20^7 - 16*a02*a20^3*a22^4 + a20^8
	@};
end function;
