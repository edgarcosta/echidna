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


function Level2ThetaNullHumbertPolynomials05(R)
    P<a00,a02,a20,a22> := PolynomialRing(R, 4 : Global);
    return {@
	2*a00^5*a02*a20*a22 - a00^4*a02^4 - a00^4*a20^4 - a00^4*a22^4 - 
	2*a00^2*a02^2*a20^2*a22^2 + 2*a00*a02^5*a20*a22 + 2*a00*a02*a20^5*a22 + 
	2*a00*a02*a20*a22^5 - a02^4*a20^4 - a02^4*a22^4 - a20^4*a22^4,
	2*a00^5*a02*a20*a22 + a00^4*a02^4 + a00^4*a20^4 + a00^4*a22^4 + 
	2*a00^2*a02^2*a20^2*a22^2 + 2*a00*a02^5*a20*a22 + 2*a00*a02*a20^5*a22 + 
	2*a00*a02*a20*a22^5 + a02^4*a20^4 + a02^4*a22^4 + a20^4*a22^4,
	a00^8 + 4*a00^6*a02^2 - 4*a00^6*a20^2 - 4*a00^6*a22^2 + 6*a00^4*a02^4 + 
	20*a00^4*a02^2*a20^2 + 20*a00^4*a02^2*a22^2 + 6*a00^4*a20^4 - 
	20*a00^4*a20^2*a22^2 + 6*a00^4*a22^4 + 4*a00^2*a02^6 + 
	20*a00^2*a02^4*a20^2 + 20*a00^2*a02^4*a22^2 - 20*a00^2*a02^2*a20^4 + 
	152*a00^2*a02^2*a20^2*a22^2 - 20*a00^2*a02^2*a22^4 - 4*a00^2*a20^6 + 
	20*a00^2*a20^4*a22^2 + 20*a00^2*a20^2*a22^4 - 4*a00^2*a22^6 + a02^8 - 
	4*a02^6*a20^2 - 4*a02^6*a22^2 + 6*a02^4*a20^4 - 20*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 - 4*a02^2*a20^6 + 20*a02^2*a20^4*a22^2 + 
	20*a02^2*a20^2*a22^4 - 4*a02^2*a22^6 + a20^8 + 4*a20^6*a22^2 + 
	6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 + 4*a00^6*a02^2 + 4*a00^6*a20^2 + 4*a00^6*a22^2 + 6*a00^4*a02^4 - 
	20*a00^4*a02^2*a20^2 - 20*a00^4*a02^2*a22^2 + 6*a00^4*a20^4 - 
	20*a00^4*a20^2*a22^2 + 6*a00^4*a22^4 + 4*a00^2*a02^6 - 
	20*a00^2*a02^4*a20^2 - 20*a00^2*a02^4*a22^2 - 20*a00^2*a02^2*a20^4 + 
	152*a00^2*a02^2*a20^2*a22^2 - 20*a00^2*a02^2*a22^4 + 4*a00^2*a20^6 - 
	20*a00^2*a20^4*a22^2 - 20*a00^2*a20^2*a22^4 + 4*a00^2*a22^6 + a02^8 + 
	4*a02^6*a20^2 + 4*a02^6*a22^2 + 6*a02^4*a20^4 - 20*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 + 4*a02^2*a20^6 - 20*a02^2*a20^4*a22^2 - 
	20*a02^2*a20^2*a22^4 + 4*a02^2*a22^6 + a20^8 + 4*a20^6*a22^2 + 
	6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 - 4*a00^6*a02^2 - 4*a00^6*a20^2 + 4*a00^6*a22^2 + 6*a00^4*a02^4 - 
	20*a00^4*a02^2*a20^2 + 20*a00^4*a02^2*a22^2 + 6*a00^4*a20^4 + 
	20*a00^4*a20^2*a22^2 + 6*a00^4*a22^4 - 4*a00^2*a02^6 + 
	20*a00^2*a02^4*a20^2 - 20*a00^2*a02^4*a22^2 + 20*a00^2*a02^2*a20^4 + 
	152*a00^2*a02^2*a20^2*a22^2 + 20*a00^2*a02^2*a22^4 - 4*a00^2*a20^6 - 
	20*a00^2*a20^4*a22^2 + 20*a00^2*a20^2*a22^4 + 4*a00^2*a22^6 + a02^8 + 
	4*a02^6*a20^2 - 4*a02^6*a22^2 + 6*a02^4*a20^4 + 20*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 + 4*a02^2*a20^6 + 20*a02^2*a20^4*a22^2 - 
	20*a02^2*a20^2*a22^4 - 4*a02^2*a22^6 + a20^8 - 4*a20^6*a22^2 + 
	6*a20^4*a22^4 - 4*a20^2*a22^6 + a22^8,
	a00^8 - 4*a00^6*a02^2 + 4*a00^6*a20^2 - 4*a00^6*a22^2 + 6*a00^4*a02^4 + 
	20*a00^4*a02^2*a20^2 - 20*a00^4*a02^2*a22^2 + 6*a00^4*a20^4 + 
	20*a00^4*a20^2*a22^2 + 6*a00^4*a22^4 - 4*a00^2*a02^6 - 
	20*a00^2*a02^4*a20^2 + 20*a00^2*a02^4*a22^2 + 20*a00^2*a02^2*a20^4 + 
	152*a00^2*a02^2*a20^2*a22^2 + 20*a00^2*a02^2*a22^4 + 4*a00^2*a20^6 + 
	20*a00^2*a20^4*a22^2 - 20*a00^2*a20^2*a22^4 - 4*a00^2*a22^6 + a02^8 - 
	4*a02^6*a20^2 + 4*a02^6*a22^2 + 6*a02^4*a20^4 + 20*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 - 4*a02^2*a20^6 - 20*a02^2*a20^4*a22^2 + 
	20*a02^2*a20^2*a22^4 + 4*a02^2*a22^6 + a20^8 - 4*a20^6*a22^2 + 
	6*a20^4*a22^4 - 4*a20^2*a22^6 + a22^8
	@};
end function;    
