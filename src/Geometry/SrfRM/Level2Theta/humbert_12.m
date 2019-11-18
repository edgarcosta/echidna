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

function Level2ThetaNullHumbertPolynomials12(R)
    P<a00,a02,a20,a22> := PolynomialRing(R, 4 : Global);
    return {@
	4*a00^2*a02*a22 - 4*a00^2*a20^2 - a02^4 - 2*a02^2*a22^2 + 4*a02*a20^2*a22 - a22^4,
	4*a00^2*a02*a22 + 4*a00^2*a20^2 + a02^4 + 2*a02^2*a22^2 + 4*a02*a20^2*a22 + a22^4,
	a00^4 + 2*a00^2*a20^2 - 4*a00*a02^2*a20 - 4*a00*a20*a22^2 + 4*a02^2*a22^2 + a20^4,
	a00^4 + 2*a00^2*a20^2 + 4*a00*a02^2*a20 + 4*a00*a20*a22^2 + 4*a02^2*a22^2 + a20^4,
	a00^4 - 4*a00^3*a02 - 4*a00^3*a20 + 4*a00^3*a22 + 6*a00^2*a02^2 - 4*a00^2*a02*a20 + 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 + 4*a00^2*a20*a22 + 6*a00^2*a22^2 - 4*a00*a02^3 + 
	4*a00*a02^2*a20 - 4*a00*a02^2*a22 + 4*a00*a02*a20^2 + 24*a00*a02*a20*a22 + 
	4*a00*a02*a22^2 - 4*a00*a20^3 - 4*a00*a20^2*a22 + 4*a00*a20*a22^2 + 4*a00*a22^3 + a02^4 
	+ 4*a02^3*a20 - 4*a02^3*a22 + 6*a02^2*a20^2 + 4*a02^2*a20*a22 + 6*a02^2*a22^2 + 
	4*a02*a20^3 + 4*a02*a20^2*a22 - 4*a02*a20*a22^2 - 4*a02*a22^3 + a20^4 - 4*a20^3*a22 + 
	6*a20^2*a22^2 - 4*a20*a22^3 + a22^4,
	a00^4 - 4*a00^3*a02 + 4*a00^3*a20 - 4*a00^3*a22 + 6*a00^2*a02^2 + 4*a00^2*a02*a20 - 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 + 4*a00^2*a20*a22 + 6*a00^2*a22^2 - 4*a00*a02^3 - 
	4*a00*a02^2*a20 + 4*a00*a02^2*a22 + 4*a00*a02*a20^2 + 24*a00*a02*a20*a22 + 
	4*a00*a02*a22^2 + 4*a00*a20^3 + 4*a00*a20^2*a22 - 4*a00*a20*a22^2 - 4*a00*a22^3 + a02^4 
	- 4*a02^3*a20 + 4*a02^3*a22 + 6*a02^2*a20^2 + 4*a02^2*a20*a22 + 6*a02^2*a22^2 - 
	4*a02*a20^3 - 4*a02*a20^2*a22 + 4*a02*a20*a22^2 + 4*a02*a22^3 + a20^4 - 4*a20^3*a22 + 
	6*a20^2*a22^2 - 4*a20*a22^3 + a22^4,
	a00^4 + 4*a00^3*a02 - 4*a00^3*a20 - 4*a00^3*a22 + 6*a00^2*a02^2 + 4*a00^2*a02*a20 + 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 - 4*a00^2*a20*a22 + 6*a00^2*a22^2 + 4*a00*a02^3 + 
	4*a00*a02^2*a20 + 4*a00*a02^2*a22 - 4*a00*a02*a20^2 + 24*a00*a02*a20*a22 - 
	4*a00*a02*a22^2 - 4*a00*a20^3 + 4*a00*a20^2*a22 + 4*a00*a20*a22^2 - 4*a00*a22^3 + a02^4 
	- 4*a02^3*a20 - 4*a02^3*a22 + 6*a02^2*a20^2 - 4*a02^2*a20*a22 + 6*a02^2*a22^2 - 
	4*a02*a20^3 + 4*a02*a20^2*a22 + 4*a02*a20*a22^2 - 4*a02*a22^3 + a20^4 + 4*a20^3*a22 + 
	6*a20^2*a22^2 + 4*a20*a22^3 + a22^4,
	a00^4 + 4*a00^3*a02 + 4*a00^3*a20 + 4*a00^3*a22 + 6*a00^2*a02^2 - 4*a00^2*a02*a20 - 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 - 4*a00^2*a20*a22 + 6*a00^2*a22^2 + 4*a00*a02^3 - 
	4*a00*a02^2*a20 - 4*a00*a02^2*a22 - 4*a00*a02*a20^2 + 24*a00*a02*a20*a22 - 
	4*a00*a02*a22^2 + 4*a00*a20^3 - 4*a00*a20^2*a22 - 4*a00*a20*a22^2 + 4*a00*a22^3 + a02^4 
	+ 4*a02^3*a20 + 4*a02^3*a22 + 6*a02^2*a20^2 - 4*a02^2*a20*a22 + 6*a02^2*a22^2 + 
	4*a02*a20^3 - 4*a02*a20^2*a22 - 4*a02*a20*a22^2 + 4*a02*a22^3 + a20^4 + 4*a20^3*a22 + 
	6*a20^2*a22^2 + 4*a20*a22^3 + a22^4,
	a00^4 - 4*a00^3*a02 - 4*a00^3*a20 - 4*a00^3*a22 + 6*a00^2*a02^2 - 4*a00^2*a02*a20 - 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 - 4*a00^2*a20*a22 + 6*a00^2*a22^2 - 4*a00*a02^3 + 
	4*a00*a02^2*a20 + 4*a00*a02^2*a22 + 4*a00*a02*a20^2 - 24*a00*a02*a20*a22 + 
	4*a00*a02*a22^2 - 4*a00*a20^3 + 4*a00*a20^2*a22 + 4*a00*a20*a22^2 - 4*a00*a22^3 + a02^4 
	+ 4*a02^3*a20 + 4*a02^3*a22 + 6*a02^2*a20^2 - 4*a02^2*a20*a22 + 6*a02^2*a22^2 + 
	4*a02*a20^3 - 4*a02*a20^2*a22 - 4*a02*a20*a22^2 + 4*a02*a22^3 + a20^4 + 4*a20^3*a22 + 
	6*a20^2*a22^2 + 4*a20*a22^3 + a22^4,
	a00^4 - 4*a00^3*a02 + 4*a00^3*a20 + 4*a00^3*a22 + 6*a00^2*a02^2 + 4*a00^2*a02*a20 + 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 - 4*a00^2*a20*a22 + 6*a00^2*a22^2 - 4*a00*a02^3 - 
	4*a00*a02^2*a20 - 4*a00*a02^2*a22 + 4*a00*a02*a20^2 - 24*a00*a02*a20*a22 + 
	4*a00*a02*a22^2 + 4*a00*a20^3 - 4*a00*a20^2*a22 - 4*a00*a20*a22^2 + 4*a00*a22^3 + a02^4 
	- 4*a02^3*a20 - 4*a02^3*a22 + 6*a02^2*a20^2 - 4*a02^2*a20*a22 + 6*a02^2*a22^2 - 
	4*a02*a20^3 + 4*a02*a20^2*a22 + 4*a02*a20*a22^2 - 4*a02*a22^3 + a20^4 + 4*a20^3*a22 + 
	6*a20^2*a22^2 + 4*a20*a22^3 + a22^4,
	a00^4 + 4*a00^3*a02 - 4*a00^3*a20 + 4*a00^3*a22 + 6*a00^2*a02^2 + 4*a00^2*a02*a20 - 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 + 4*a00^2*a20*a22 + 6*a00^2*a22^2 + 4*a00*a02^3 + 
	4*a00*a02^2*a20 - 4*a00*a02^2*a22 - 4*a00*a02*a20^2 - 24*a00*a02*a20*a22 - 
	4*a00*a02*a22^2 - 4*a00*a20^3 - 4*a00*a20^2*a22 + 4*a00*a20*a22^2 + 4*a00*a22^3 + a02^4 
	- 4*a02^3*a20 + 4*a02^3*a22 + 6*a02^2*a20^2 + 4*a02^2*a20*a22 + 6*a02^2*a22^2 - 
	4*a02*a20^3 - 4*a02*a20^2*a22 + 4*a02*a20*a22^2 + 4*a02*a22^3 + a20^4 - 4*a20^3*a22 + 
	6*a20^2*a22^2 - 4*a20*a22^3 + a22^4,
	a00^4 + 4*a00^3*a02 + 4*a00^3*a20 - 4*a00^3*a22 + 6*a00^2*a02^2 - 4*a00^2*a02*a20 + 
	4*a00^2*a02*a22 + 6*a00^2*a20^2 + 4*a00^2*a20*a22 + 6*a00^2*a22^2 + 4*a00*a02^3 - 
	4*a00*a02^2*a20 + 4*a00*a02^2*a22 - 4*a00*a02*a20^2 - 24*a00*a02*a20*a22 - 
	4*a00*a02*a22^2 + 4*a00*a20^3 + 4*a00*a20^2*a22 - 4*a00*a20*a22^2 - 4*a00*a22^3 + a02^4 
	+ 4*a02^3*a20 - 4*a02^3*a22 + 6*a02^2*a20^2 + 4*a02^2*a20*a22 + 6*a02^2*a22^2 + 
	4*a02*a20^3 + 4*a02*a20^2*a22 - 4*a02*a20*a22^2 - 4*a02*a22^3 + a20^4 - 4*a20^3*a22 + 
	6*a20^2*a22^2 - 4*a20*a22^3 + a22^4,
	a00^8 - 8*a00^7*a22 + 4*a00^6*a02^2 - 40*a00^6*a02*a20 + 4*a00^6*a20^2 + 28*a00^6*a22^2 + 
	72*a00^5*a02^2*a22 - 80*a00^5*a02*a20*a22 + 72*a00^5*a20^2*a22 - 56*a00^5*a22^3 + 
	6*a00^4*a02^4 + 40*a00^4*a02^3*a20 + 164*a00^4*a02^2*a20^2 - 68*a00^4*a02^2*a22^2 + 
	40*a00^4*a02*a20^3 + 168*a00^4*a02*a20*a22^2 + 6*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	70*a00^4*a22^4 + 40*a00^3*a02^4*a22 + 352*a00^3*a02^3*a20*a22 + 
	240*a00^3*a02^2*a20^2*a22 - 16*a00^3*a02^2*a22^3 + 352*a00^3*a02*a20^3*a22 - 
	96*a00^3*a02*a20*a22^3 + 40*a00^3*a20^4*a22 - 16*a00^3*a20^2*a22^3 - 56*a00^3*a22^5 + 
	4*a00^2*a02^6 + 72*a00^2*a02^5*a20 - 68*a00^2*a02^4*a20^2 + 164*a00^2*a02^4*a22^2 - 
	16*a00^2*a02^3*a20^3 + 240*a00^2*a02^3*a20*a22^2 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 + 72*a00^2*a02*a20^5 + 
	240*a00^2*a02*a20^3*a22^2 + 168*a00^2*a02*a20*a22^4 + 4*a00^2*a20^6 + 
	164*a00^2*a20^4*a22^2 - 68*a00^2*a20^2*a22^4 + 28*a00^2*a22^6 - 40*a00*a02^6*a22 - 
	80*a00*a02^5*a20*a22 + 168*a00*a02^4*a20^2*a22 + 40*a00*a02^4*a22^3 - 
	96*a00*a02^3*a20^3*a22 + 352*a00*a02^3*a20*a22^3 + 168*a00*a02^2*a20^4*a22 + 
	240*a00*a02^2*a20^2*a22^3 + 72*a00*a02^2*a22^5 - 80*a00*a02*a20^5*a22 + 
	352*a00*a02*a20^3*a22^3 - 80*a00*a02*a20*a22^5 - 40*a00*a20^6*a22 + 40*a00*a20^4*a22^3 +
	72*a00*a20^2*a22^5 - 8*a00*a22^7 + a02^8 - 8*a02^7*a20 + 28*a02^6*a20^2 + 4*a02^6*a22^2 
	- 56*a02^5*a20^3 + 72*a02^5*a20*a22^2 + 70*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 - 56*a02^3*a20^5 - 16*a02^3*a20^3*a22^2 + 40*a02^3*a20*a22^4 + 
	28*a02^2*a20^6 - 68*a02^2*a20^4*a22^2 + 164*a02^2*a20^2*a22^4 + 4*a02^2*a22^6 - 
	8*a02*a20^7 + 72*a02*a20^5*a22^2 + 40*a02*a20^3*a22^4 - 40*a02*a20*a22^6 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 + 8*a00^7*a22 + 4*a00^6*a02^2 + 40*a00^6*a02*a20 + 4*a00^6*a20^2 + 28*a00^6*a22^2 - 
	72*a00^5*a02^2*a22 - 80*a00^5*a02*a20*a22 - 72*a00^5*a20^2*a22 + 56*a00^5*a22^3 + 
	6*a00^4*a02^4 - 40*a00^4*a02^3*a20 + 164*a00^4*a02^2*a20^2 - 68*a00^4*a02^2*a22^2 - 
	40*a00^4*a02*a20^3 - 168*a00^4*a02*a20*a22^2 + 6*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	70*a00^4*a22^4 - 40*a00^3*a02^4*a22 + 352*a00^3*a02^3*a20*a22 - 
	240*a00^3*a02^2*a20^2*a22 + 16*a00^3*a02^2*a22^3 + 352*a00^3*a02*a20^3*a22 - 
	96*a00^3*a02*a20*a22^3 - 40*a00^3*a20^4*a22 + 16*a00^3*a20^2*a22^3 + 56*a00^3*a22^5 + 
	4*a00^2*a02^6 - 72*a00^2*a02^5*a20 - 68*a00^2*a02^4*a20^2 + 164*a00^2*a02^4*a22^2 + 
	16*a00^2*a02^3*a20^3 - 240*a00^2*a02^3*a20*a22^2 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 - 72*a00^2*a02*a20^5 - 
	240*a00^2*a02*a20^3*a22^2 - 168*a00^2*a02*a20*a22^4 + 4*a00^2*a20^6 + 
	164*a00^2*a20^4*a22^2 - 68*a00^2*a20^2*a22^4 + 28*a00^2*a22^6 + 40*a00*a02^6*a22 - 
	80*a00*a02^5*a20*a22 - 168*a00*a02^4*a20^2*a22 - 40*a00*a02^4*a22^3 - 
	96*a00*a02^3*a20^3*a22 + 352*a00*a02^3*a20*a22^3 - 168*a00*a02^2*a20^4*a22 - 
	240*a00*a02^2*a20^2*a22^3 - 72*a00*a02^2*a22^5 - 80*a00*a02*a20^5*a22 + 
	352*a00*a02*a20^3*a22^3 - 80*a00*a02*a20*a22^5 + 40*a00*a20^6*a22 - 40*a00*a20^4*a22^3 -
	72*a00*a20^2*a22^5 + 8*a00*a22^7 + a02^8 + 8*a02^7*a20 + 28*a02^6*a20^2 + 4*a02^6*a22^2 
	+ 56*a02^5*a20^3 - 72*a02^5*a20*a22^2 + 70*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 + 56*a02^3*a20^5 + 16*a02^3*a20^3*a22^2 - 40*a02^3*a20*a22^4 + 
	28*a02^2*a20^6 - 68*a02^2*a20^4*a22^2 + 164*a02^2*a20^2*a22^4 + 4*a02^2*a22^6 + 
	8*a02*a20^7 - 72*a02*a20^5*a22^2 - 40*a02*a20^3*a22^4 + 40*a02*a20*a22^6 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 - 8*a00^7*a22 + 4*a00^6*a02^2 + 40*a00^6*a02*a20 + 4*a00^6*a20^2 + 28*a00^6*a22^2 + 
	72*a00^5*a02^2*a22 + 80*a00^5*a02*a20*a22 + 72*a00^5*a20^2*a22 - 56*a00^5*a22^3 + 
	6*a00^4*a02^4 - 40*a00^4*a02^3*a20 + 164*a00^4*a02^2*a20^2 - 68*a00^4*a02^2*a22^2 - 
	40*a00^4*a02*a20^3 - 168*a00^4*a02*a20*a22^2 + 6*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	70*a00^4*a22^4 + 40*a00^3*a02^4*a22 - 352*a00^3*a02^3*a20*a22 + 
	240*a00^3*a02^2*a20^2*a22 - 16*a00^3*a02^2*a22^3 - 352*a00^3*a02*a20^3*a22 + 
	96*a00^3*a02*a20*a22^3 + 40*a00^3*a20^4*a22 - 16*a00^3*a20^2*a22^3 - 56*a00^3*a22^5 + 
	4*a00^2*a02^6 - 72*a00^2*a02^5*a20 - 68*a00^2*a02^4*a20^2 + 164*a00^2*a02^4*a22^2 + 
	16*a00^2*a02^3*a20^3 - 240*a00^2*a02^3*a20*a22^2 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 - 72*a00^2*a02*a20^5 - 
	240*a00^2*a02*a20^3*a22^2 - 168*a00^2*a02*a20*a22^4 + 4*a00^2*a20^6 + 
	164*a00^2*a20^4*a22^2 - 68*a00^2*a20^2*a22^4 + 28*a00^2*a22^6 - 40*a00*a02^6*a22 + 
	80*a00*a02^5*a20*a22 + 168*a00*a02^4*a20^2*a22 + 40*a00*a02^4*a22^3 + 
	96*a00*a02^3*a20^3*a22 - 352*a00*a02^3*a20*a22^3 + 168*a00*a02^2*a20^4*a22 + 
	240*a00*a02^2*a20^2*a22^3 + 72*a00*a02^2*a22^5 + 80*a00*a02*a20^5*a22 - 
	352*a00*a02*a20^3*a22^3 + 80*a00*a02*a20*a22^5 - 40*a00*a20^6*a22 + 40*a00*a20^4*a22^3 +
	72*a00*a20^2*a22^5 - 8*a00*a22^7 + a02^8 + 8*a02^7*a20 + 28*a02^6*a20^2 + 4*a02^6*a22^2 
	+ 56*a02^5*a20^3 - 72*a02^5*a20*a22^2 + 70*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 + 56*a02^3*a20^5 + 16*a02^3*a20^3*a22^2 - 40*a02^3*a20*a22^4 + 
	28*a02^2*a20^6 - 68*a02^2*a20^4*a22^2 + 164*a02^2*a20^2*a22^4 + 4*a02^2*a22^6 + 
	8*a02*a20^7 - 72*a02*a20^5*a22^2 - 40*a02*a20^3*a22^4 + 40*a02*a20*a22^6 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 + 8*a00^7*a22 + 4*a00^6*a02^2 - 40*a00^6*a02*a20 + 4*a00^6*a20^2 + 28*a00^6*a22^2 - 
	72*a00^5*a02^2*a22 + 80*a00^5*a02*a20*a22 - 72*a00^5*a20^2*a22 + 56*a00^5*a22^3 + 
	6*a00^4*a02^4 + 40*a00^4*a02^3*a20 + 164*a00^4*a02^2*a20^2 - 68*a00^4*a02^2*a22^2 + 
	40*a00^4*a02*a20^3 + 168*a00^4*a02*a20*a22^2 + 6*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	70*a00^4*a22^4 - 40*a00^3*a02^4*a22 - 352*a00^3*a02^3*a20*a22 - 
	240*a00^3*a02^2*a20^2*a22 + 16*a00^3*a02^2*a22^3 - 352*a00^3*a02*a20^3*a22 + 
	96*a00^3*a02*a20*a22^3 - 40*a00^3*a20^4*a22 + 16*a00^3*a20^2*a22^3 + 56*a00^3*a22^5 + 
	4*a00^2*a02^6 + 72*a00^2*a02^5*a20 - 68*a00^2*a02^4*a20^2 + 164*a00^2*a02^4*a22^2 - 
	16*a00^2*a02^3*a20^3 + 240*a00^2*a02^3*a20*a22^2 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 + 72*a00^2*a02*a20^5 + 
	240*a00^2*a02*a20^3*a22^2 + 168*a00^2*a02*a20*a22^4 + 4*a00^2*a20^6 + 
	164*a00^2*a20^4*a22^2 - 68*a00^2*a20^2*a22^4 + 28*a00^2*a22^6 + 40*a00*a02^6*a22 + 
	80*a00*a02^5*a20*a22 - 168*a00*a02^4*a20^2*a22 - 40*a00*a02^4*a22^3 + 
	96*a00*a02^3*a20^3*a22 - 352*a00*a02^3*a20*a22^3 - 168*a00*a02^2*a20^4*a22 - 
	240*a00*a02^2*a20^2*a22^3 - 72*a00*a02^2*a22^5 + 80*a00*a02*a20^5*a22 - 
	352*a00*a02*a20^3*a22^3 + 80*a00*a02*a20*a22^5 + 40*a00*a20^6*a22 - 40*a00*a20^4*a22^3 -
	72*a00*a20^2*a22^5 + 8*a00*a22^7 + a02^8 - 8*a02^7*a20 + 28*a02^6*a20^2 + 4*a02^6*a22^2 
	- 56*a02^5*a20^3 + 72*a02^5*a20*a22^2 + 70*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	6*a02^4*a22^4 - 56*a02^3*a20^5 - 16*a02^3*a20^3*a22^2 + 40*a02^3*a20*a22^4 + 
	28*a02^2*a20^6 - 68*a02^2*a20^4*a22^2 + 164*a02^2*a20^2*a22^4 + 4*a02^2*a22^6 - 
	8*a02*a20^7 + 72*a02*a20^5*a22^2 + 40*a02*a20^3*a22^4 - 40*a02*a20*a22^6 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	16*a00^4*a02^4 + 16*a00^4*a20^2*a22^2 - 8*a00^2*a02^2*a20^4 - 16*a00^2*a02^2*a20^2*a22^2 - 
	8*a00^2*a02^2*a22^4 + 16*a02^4*a20^2*a22^2 + a20^8 - 4*a20^6*a22^2 + 6*a20^4*a22^4 - 
	4*a20^2*a22^6 + a22^8,
	a00^8 - 4*a00^6*a02^2 + 6*a00^4*a02^4 - 8*a00^4*a20^2*a22^2 - 4*a00^2*a02^6 + 
	16*a00^2*a02^2*a20^4 - 16*a00^2*a02^2*a20^2*a22^2 + 16*a00^2*a02^2*a22^4 + a02^8 - 
	8*a02^4*a20^2*a22^2 + 16*a20^4*a22^4,
	a00^4 - 2*a00^2*a02^2 - 2*a00^2*a20^2 + 2*a00^2*a22^2 + a02^4 - 2*a02^2*a20^2 + 
	2*a02^2*a22^2 + a20^4 + 2*a20^2*a22^2 + a22^4,
	a00^4 - 2*a00^2*a02^2 + 2*a00^2*a20^2 - 2*a00^2*a22^2 + a02^4 + 2*a02^2*a20^2 - 
	2*a02^2*a22^2 + a20^4 + 2*a20^2*a22^2 + a22^4,
	a00^4 + 2*a00^2*a02^2 - 2*a00^2*a20^2 - 2*a00^2*a22^2 + a02^4 + 2*a02^2*a20^2 + 
	2*a02^2*a22^2 + a20^4 - 2*a20^2*a22^2 + a22^4,
	a00^4 + 2*a00^2*a02^2 + 2*a00^2*a20^2 + 2*a00^2*a22^2 + a02^4 - 2*a02^2*a20^2 - 
	2*a02^2*a22^2 + a20^4 - 2*a20^2*a22^2 + a22^4,
	a00^8 - 8*a00^7*a02 + 28*a00^6*a02^2 + 4*a00^6*a20^2 - 40*a00^6*a20*a22 + 4*a00^6*a22^2 - 
	56*a00^5*a02^3 + 72*a00^5*a02*a20^2 - 80*a00^5*a02*a20*a22 + 72*a00^5*a02*a22^2 + 
	70*a00^4*a02^4 - 68*a00^4*a02^2*a20^2 + 168*a00^4*a02^2*a20*a22 - 68*a00^4*a02^2*a22^2 +
	6*a00^4*a20^4 + 40*a00^4*a20^3*a22 + 164*a00^4*a20^2*a22^2 + 40*a00^4*a20*a22^3 + 
	6*a00^4*a22^4 - 56*a00^3*a02^5 - 16*a00^3*a02^3*a20^2 - 96*a00^3*a02^3*a20*a22 - 
	16*a00^3*a02^3*a22^2 + 40*a00^3*a02*a20^4 + 352*a00^3*a02*a20^3*a22 + 
	240*a00^3*a02*a20^2*a22^2 + 352*a00^3*a02*a20*a22^3 + 40*a00^3*a02*a22^4 + 
	28*a00^2*a02^6 - 68*a00^2*a02^4*a20^2 + 168*a00^2*a02^4*a20*a22 - 68*a00^2*a02^4*a22^2 +
	164*a00^2*a02^2*a20^4 + 240*a00^2*a02^2*a20^3*a22 + 728*a00^2*a02^2*a20^2*a22^2 + 
	240*a00^2*a02^2*a20*a22^3 + 164*a00^2*a02^2*a22^4 + 4*a00^2*a20^6 + 72*a00^2*a20^5*a22 -
	68*a00^2*a20^4*a22^2 - 16*a00^2*a20^3*a22^3 - 68*a00^2*a20^2*a22^4 + 72*a00^2*a20*a22^5 
	+ 4*a00^2*a22^6 - 8*a00*a02^7 + 72*a00*a02^5*a20^2 - 80*a00*a02^5*a20*a22 + 
	72*a00*a02^5*a22^2 + 40*a00*a02^3*a20^4 + 352*a00*a02^3*a20^3*a22 + 
	240*a00*a02^3*a20^2*a22^2 + 352*a00*a02^3*a20*a22^3 + 40*a00*a02^3*a22^4 - 
	40*a00*a02*a20^6 - 80*a00*a02*a20^5*a22 + 168*a00*a02*a20^4*a22^2 - 
	96*a00*a02*a20^3*a22^3 + 168*a00*a02*a20^2*a22^4 - 80*a00*a02*a20*a22^5 - 
	40*a00*a02*a22^6 + a02^8 + 4*a02^6*a20^2 - 40*a02^6*a20*a22 + 4*a02^6*a22^2 + 
	6*a02^4*a20^4 + 40*a02^4*a20^3*a22 + 164*a02^4*a20^2*a22^2 + 40*a02^4*a20*a22^3 + 
	6*a02^4*a22^4 + 4*a02^2*a20^6 + 72*a02^2*a20^5*a22 - 68*a02^2*a20^4*a22^2 - 
	16*a02^2*a20^3*a22^3 - 68*a02^2*a20^2*a22^4 + 72*a02^2*a20*a22^5 + 4*a02^2*a22^6 + a20^8
	- 8*a20^7*a22 + 28*a20^6*a22^2 - 56*a20^5*a22^3 + 70*a20^4*a22^4 - 56*a20^3*a22^5 + 
	28*a20^2*a22^6 - 8*a20*a22^7 + a22^8,
	a00^8 + 8*a00^7*a02 + 28*a00^6*a02^2 + 4*a00^6*a20^2 + 40*a00^6*a20*a22 + 4*a00^6*a22^2 + 
	56*a00^5*a02^3 - 72*a00^5*a02*a20^2 - 80*a00^5*a02*a20*a22 - 72*a00^5*a02*a22^2 + 
	70*a00^4*a02^4 - 68*a00^4*a02^2*a20^2 - 168*a00^4*a02^2*a20*a22 - 68*a00^4*a02^2*a22^2 +
	6*a00^4*a20^4 - 40*a00^4*a20^3*a22 + 164*a00^4*a20^2*a22^2 - 40*a00^4*a20*a22^3 + 
	6*a00^4*a22^4 + 56*a00^3*a02^5 + 16*a00^3*a02^3*a20^2 - 96*a00^3*a02^3*a20*a22 + 
	16*a00^3*a02^3*a22^2 - 40*a00^3*a02*a20^4 + 352*a00^3*a02*a20^3*a22 - 
	240*a00^3*a02*a20^2*a22^2 + 352*a00^3*a02*a20*a22^3 - 40*a00^3*a02*a22^4 + 
	28*a00^2*a02^6 - 68*a00^2*a02^4*a20^2 - 168*a00^2*a02^4*a20*a22 - 68*a00^2*a02^4*a22^2 +
	164*a00^2*a02^2*a20^4 - 240*a00^2*a02^2*a20^3*a22 + 728*a00^2*a02^2*a20^2*a22^2 - 
	240*a00^2*a02^2*a20*a22^3 + 164*a00^2*a02^2*a22^4 + 4*a00^2*a20^6 - 72*a00^2*a20^5*a22 -
	68*a00^2*a20^4*a22^2 + 16*a00^2*a20^3*a22^3 - 68*a00^2*a20^2*a22^4 - 72*a00^2*a20*a22^5 
	+ 4*a00^2*a22^6 + 8*a00*a02^7 - 72*a00*a02^5*a20^2 - 80*a00*a02^5*a20*a22 - 
	72*a00*a02^5*a22^2 - 40*a00*a02^3*a20^4 + 352*a00*a02^3*a20^3*a22 - 
	240*a00*a02^3*a20^2*a22^2 + 352*a00*a02^3*a20*a22^3 - 40*a00*a02^3*a22^4 + 
	40*a00*a02*a20^6 - 80*a00*a02*a20^5*a22 - 168*a00*a02*a20^4*a22^2 - 
	96*a00*a02*a20^3*a22^3 - 168*a00*a02*a20^2*a22^4 - 80*a00*a02*a20*a22^5 + 
	40*a00*a02*a22^6 + a02^8 + 4*a02^6*a20^2 + 40*a02^6*a20*a22 + 4*a02^6*a22^2 + 
	6*a02^4*a20^4 - 40*a02^4*a20^3*a22 + 164*a02^4*a20^2*a22^2 - 40*a02^4*a20*a22^3 + 
	6*a02^4*a22^4 + 4*a02^2*a20^6 - 72*a02^2*a20^5*a22 - 68*a02^2*a20^4*a22^2 + 
	16*a02^2*a20^3*a22^3 - 68*a02^2*a20^2*a22^4 - 72*a02^2*a20*a22^5 + 4*a02^2*a22^6 + a20^8
	+ 8*a20^7*a22 + 28*a20^6*a22^2 + 56*a20^5*a22^3 + 70*a20^4*a22^4 + 56*a20^3*a22^5 + 
	28*a20^2*a22^6 + 8*a20*a22^7 + a22^8,
	a00^8 - 8*a00^7*a02 + 28*a00^6*a02^2 + 4*a00^6*a20^2 + 40*a00^6*a20*a22 + 4*a00^6*a22^2 - 
	56*a00^5*a02^3 + 72*a00^5*a02*a20^2 + 80*a00^5*a02*a20*a22 + 72*a00^5*a02*a22^2 + 
	70*a00^4*a02^4 - 68*a00^4*a02^2*a20^2 - 168*a00^4*a02^2*a20*a22 - 68*a00^4*a02^2*a22^2 +
	6*a00^4*a20^4 - 40*a00^4*a20^3*a22 + 164*a00^4*a20^2*a22^2 - 40*a00^4*a20*a22^3 + 
	6*a00^4*a22^4 - 56*a00^3*a02^5 - 16*a00^3*a02^3*a20^2 + 96*a00^3*a02^3*a20*a22 - 
	16*a00^3*a02^3*a22^2 + 40*a00^3*a02*a20^4 - 352*a00^3*a02*a20^3*a22 + 
	240*a00^3*a02*a20^2*a22^2 - 352*a00^3*a02*a20*a22^3 + 40*a00^3*a02*a22^4 + 
	28*a00^2*a02^6 - 68*a00^2*a02^4*a20^2 - 168*a00^2*a02^4*a20*a22 - 68*a00^2*a02^4*a22^2 +
	164*a00^2*a02^2*a20^4 - 240*a00^2*a02^2*a20^3*a22 + 728*a00^2*a02^2*a20^2*a22^2 - 
	240*a00^2*a02^2*a20*a22^3 + 164*a00^2*a02^2*a22^4 + 4*a00^2*a20^6 - 72*a00^2*a20^5*a22 -
	68*a00^2*a20^4*a22^2 + 16*a00^2*a20^3*a22^3 - 68*a00^2*a20^2*a22^4 - 72*a00^2*a20*a22^5 
	+ 4*a00^2*a22^6 - 8*a00*a02^7 + 72*a00*a02^5*a20^2 + 80*a00*a02^5*a20*a22 + 
	72*a00*a02^5*a22^2 + 40*a00*a02^3*a20^4 - 352*a00*a02^3*a20^3*a22 + 
	240*a00*a02^3*a20^2*a22^2 - 352*a00*a02^3*a20*a22^3 + 40*a00*a02^3*a22^4 - 
	40*a00*a02*a20^6 + 80*a00*a02*a20^5*a22 + 168*a00*a02*a20^4*a22^2 + 
	96*a00*a02*a20^3*a22^3 + 168*a00*a02*a20^2*a22^4 + 80*a00*a02*a20*a22^5 - 
	40*a00*a02*a22^6 + a02^8 + 4*a02^6*a20^2 + 40*a02^6*a20*a22 + 4*a02^6*a22^2 + 
	6*a02^4*a20^4 - 40*a02^4*a20^3*a22 + 164*a02^4*a20^2*a22^2 - 40*a02^4*a20*a22^3 + 
	6*a02^4*a22^4 + 4*a02^2*a20^6 - 72*a02^2*a20^5*a22 - 68*a02^2*a20^4*a22^2 + 
	16*a02^2*a20^3*a22^3 - 68*a02^2*a20^2*a22^4 - 72*a02^2*a20*a22^5 + 4*a02^2*a22^6 + a20^8
	+ 8*a20^7*a22 + 28*a20^6*a22^2 + 56*a20^5*a22^3 + 70*a20^4*a22^4 + 56*a20^3*a22^5 + 
	28*a20^2*a22^6 + 8*a20*a22^7 + a22^8,
	a00^8 + 8*a00^7*a02 + 28*a00^6*a02^2 + 4*a00^6*a20^2 - 40*a00^6*a20*a22 + 4*a00^6*a22^2 + 
	56*a00^5*a02^3 - 72*a00^5*a02*a20^2 + 80*a00^5*a02*a20*a22 - 72*a00^5*a02*a22^2 + 
	70*a00^4*a02^4 - 68*a00^4*a02^2*a20^2 + 168*a00^4*a02^2*a20*a22 - 68*a00^4*a02^2*a22^2 +
	6*a00^4*a20^4 + 40*a00^4*a20^3*a22 + 164*a00^4*a20^2*a22^2 + 40*a00^4*a20*a22^3 + 
	6*a00^4*a22^4 + 56*a00^3*a02^5 + 16*a00^3*a02^3*a20^2 + 96*a00^3*a02^3*a20*a22 + 
	16*a00^3*a02^3*a22^2 - 40*a00^3*a02*a20^4 - 352*a00^3*a02*a20^3*a22 - 
	240*a00^3*a02*a20^2*a22^2 - 352*a00^3*a02*a20*a22^3 - 40*a00^3*a02*a22^4 + 
	28*a00^2*a02^6 - 68*a00^2*a02^4*a20^2 + 168*a00^2*a02^4*a20*a22 - 68*a00^2*a02^4*a22^2 +
	164*a00^2*a02^2*a20^4 + 240*a00^2*a02^2*a20^3*a22 + 728*a00^2*a02^2*a20^2*a22^2 + 
	240*a00^2*a02^2*a20*a22^3 + 164*a00^2*a02^2*a22^4 + 4*a00^2*a20^6 + 72*a00^2*a20^5*a22 -
	68*a00^2*a20^4*a22^2 - 16*a00^2*a20^3*a22^3 - 68*a00^2*a20^2*a22^4 + 72*a00^2*a20*a22^5 
	+ 4*a00^2*a22^6 + 8*a00*a02^7 - 72*a00*a02^5*a20^2 + 80*a00*a02^5*a20*a22 - 
	72*a00*a02^5*a22^2 - 40*a00*a02^3*a20^4 - 352*a00*a02^3*a20^3*a22 - 
	240*a00*a02^3*a20^2*a22^2 - 352*a00*a02^3*a20*a22^3 - 40*a00*a02^3*a22^4 + 
	40*a00*a02*a20^6 + 80*a00*a02*a20^5*a22 - 168*a00*a02*a20^4*a22^2 + 
	96*a00*a02*a20^3*a22^3 - 168*a00*a02*a20^2*a22^4 + 80*a00*a02*a20*a22^5 + 
	40*a00*a02*a22^6 + a02^8 + 4*a02^6*a20^2 - 40*a02^6*a20*a22 + 4*a02^6*a22^2 + 
	6*a02^4*a20^4 + 40*a02^4*a20^3*a22 + 164*a02^4*a20^2*a22^2 + 40*a02^4*a20*a22^3 + 
	6*a02^4*a22^4 + 4*a02^2*a20^6 + 72*a02^2*a20^5*a22 - 68*a02^2*a20^4*a22^2 - 
	16*a02^2*a20^3*a22^3 - 68*a02^2*a20^2*a22^4 + 72*a02^2*a20*a22^5 + 4*a02^2*a22^6 + a20^8
	- 8*a20^7*a22 + 28*a20^6*a22^2 - 56*a20^5*a22^3 + 70*a20^4*a22^4 - 56*a20^3*a22^5 + 
	28*a20^2*a22^6 - 8*a20*a22^7 + a22^8,
	4*a00^2*a02^2 - 4*a00^2*a20*a22 - 4*a02^2*a20*a22 + a20^4 + 2*a20^2*a22^2 + a22^4,
	4*a00^2*a02^2 + 4*a00^2*a20*a22 + 4*a02^2*a20*a22 + a20^4 + 2*a20^2*a22^2 + a22^4,
	a00^4 + 2*a00^2*a02^2 - 4*a00*a02*a20^2 - 4*a00*a02*a22^2 + a02^4 + 4*a20^2*a22^2,
	a00^4 + 2*a00^2*a02^2 + 4*a00*a02*a20^2 + 4*a00*a02*a22^2 + a02^4 + 4*a20^2*a22^2,
	16*a00^4*a02^2*a22^2 + 16*a00^4*a20^4 - 8*a00^2*a02^4*a20^2 - 16*a00^2*a02^2*a20^2*a22^2 - 
	8*a00^2*a20^2*a22^4 + a02^8 - 4*a02^6*a22^2 + 6*a02^4*a22^4 + 16*a02^2*a20^4*a22^2 - 
	4*a02^2*a22^6 + a22^8,
	a00^8 - 4*a00^6*a20^2 - 8*a00^4*a02^2*a22^2 + 6*a00^4*a20^4 + 16*a00^2*a02^4*a20^2 - 
	16*a00^2*a02^2*a20^2*a22^2 - 4*a00^2*a20^6 + 16*a00^2*a20^2*a22^4 + 16*a02^4*a22^4 - 
	8*a02^2*a20^4*a22^2 + a20^8,
	a00^8 - 8*a00^7*a20 + 4*a00^6*a02^2 + 40*a00^6*a02*a22 + 28*a00^6*a20^2 + 4*a00^6*a22^2 + 
	72*a00^5*a02^2*a20 + 80*a00^5*a02*a20*a22 - 56*a00^5*a20^3 + 72*a00^5*a20*a22^2 + 
	6*a00^4*a02^4 - 40*a00^4*a02^3*a22 - 68*a00^4*a02^2*a20^2 + 164*a00^4*a02^2*a22^2 - 
	168*a00^4*a02*a20^2*a22 - 40*a00^4*a02*a22^3 + 70*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	6*a00^4*a22^4 + 40*a00^3*a02^4*a20 - 352*a00^3*a02^3*a20*a22 - 16*a00^3*a02^2*a20^3 + 
	240*a00^3*a02^2*a20*a22^2 + 96*a00^3*a02*a20^3*a22 - 352*a00^3*a02*a20*a22^3 - 
	56*a00^3*a20^5 - 16*a00^3*a20^3*a22^2 + 40*a00^3*a20*a22^4 + 4*a00^2*a02^6 - 
	72*a00^2*a02^5*a22 + 164*a00^2*a02^4*a20^2 - 68*a00^2*a02^4*a22^2 - 
	240*a00^2*a02^3*a20^2*a22 + 16*a00^2*a02^3*a22^3 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 - 168*a00^2*a02*a20^4*a22 - 
	240*a00^2*a02*a20^2*a22^3 - 72*a00^2*a02*a22^5 + 28*a00^2*a20^6 - 68*a00^2*a20^4*a22^2 +
	164*a00^2*a20^2*a22^4 + 4*a00^2*a22^6 - 40*a00*a02^6*a20 + 80*a00*a02^5*a20*a22 + 
	40*a00*a02^4*a20^3 + 168*a00*a02^4*a20*a22^2 - 352*a00*a02^3*a20^3*a22 + 
	96*a00*a02^3*a20*a22^3 + 72*a00*a02^2*a20^5 + 240*a00*a02^2*a20^3*a22^2 + 
	168*a00*a02^2*a20*a22^4 + 80*a00*a02*a20^5*a22 - 352*a00*a02*a20^3*a22^3 + 
	80*a00*a02*a20*a22^5 - 8*a00*a20^7 + 72*a00*a20^5*a22^2 + 40*a00*a20^3*a22^4 - 
	40*a00*a20*a22^6 + a02^8 + 8*a02^7*a22 + 4*a02^6*a20^2 + 28*a02^6*a22^2 - 
	72*a02^5*a20^2*a22 + 56*a02^5*a22^3 + 6*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	70*a02^4*a22^4 - 40*a02^3*a20^4*a22 + 16*a02^3*a20^2*a22^3 + 56*a02^3*a22^5 + 
	4*a02^2*a20^6 + 164*a02^2*a20^4*a22^2 - 68*a02^2*a20^2*a22^4 + 28*a02^2*a22^6 + 
	40*a02*a20^6*a22 - 40*a02*a20^4*a22^3 - 72*a02*a20^2*a22^5 + 8*a02*a22^7 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 + 8*a00^7*a20 + 4*a00^6*a02^2 - 40*a00^6*a02*a22 + 28*a00^6*a20^2 + 4*a00^6*a22^2 - 
	72*a00^5*a02^2*a20 + 80*a00^5*a02*a20*a22 + 56*a00^5*a20^3 - 72*a00^5*a20*a22^2 + 
	6*a00^4*a02^4 + 40*a00^4*a02^3*a22 - 68*a00^4*a02^2*a20^2 + 164*a00^4*a02^2*a22^2 + 
	168*a00^4*a02*a20^2*a22 + 40*a00^4*a02*a22^3 + 70*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	6*a00^4*a22^4 - 40*a00^3*a02^4*a20 - 352*a00^3*a02^3*a20*a22 + 16*a00^3*a02^2*a20^3 - 
	240*a00^3*a02^2*a20*a22^2 + 96*a00^3*a02*a20^3*a22 - 352*a00^3*a02*a20*a22^3 + 
	56*a00^3*a20^5 + 16*a00^3*a20^3*a22^2 - 40*a00^3*a20*a22^4 + 4*a00^2*a02^6 + 
	72*a00^2*a02^5*a22 + 164*a00^2*a02^4*a20^2 - 68*a00^2*a02^4*a22^2 + 
	240*a00^2*a02^3*a20^2*a22 - 16*a00^2*a02^3*a22^3 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 + 168*a00^2*a02*a20^4*a22 + 
	240*a00^2*a02*a20^2*a22^3 + 72*a00^2*a02*a22^5 + 28*a00^2*a20^6 - 68*a00^2*a20^4*a22^2 +
	164*a00^2*a20^2*a22^4 + 4*a00^2*a22^6 + 40*a00*a02^6*a20 + 80*a00*a02^5*a20*a22 - 
	40*a00*a02^4*a20^3 - 168*a00*a02^4*a20*a22^2 - 352*a00*a02^3*a20^3*a22 + 
	96*a00*a02^3*a20*a22^3 - 72*a00*a02^2*a20^5 - 240*a00*a02^2*a20^3*a22^2 - 
	168*a00*a02^2*a20*a22^4 + 80*a00*a02*a20^5*a22 - 352*a00*a02*a20^3*a22^3 + 
	80*a00*a02*a20*a22^5 + 8*a00*a20^7 - 72*a00*a20^5*a22^2 - 40*a00*a20^3*a22^4 + 
	40*a00*a20*a22^6 + a02^8 - 8*a02^7*a22 + 4*a02^6*a20^2 + 28*a02^6*a22^2 + 
	72*a02^5*a20^2*a22 - 56*a02^5*a22^3 + 6*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	70*a02^4*a22^4 + 40*a02^3*a20^4*a22 - 16*a02^3*a20^2*a22^3 - 56*a02^3*a22^5 + 
	4*a02^2*a20^6 + 164*a02^2*a20^4*a22^2 - 68*a02^2*a20^2*a22^4 + 28*a02^2*a22^6 - 
	40*a02*a20^6*a22 + 40*a02*a20^4*a22^3 + 72*a02*a20^2*a22^5 - 8*a02*a22^7 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 - 8*a00^7*a20 + 4*a00^6*a02^2 - 40*a00^6*a02*a22 + 28*a00^6*a20^2 + 4*a00^6*a22^2 + 
	72*a00^5*a02^2*a20 - 80*a00^5*a02*a20*a22 - 56*a00^5*a20^3 + 72*a00^5*a20*a22^2 + 
	6*a00^4*a02^4 + 40*a00^4*a02^3*a22 - 68*a00^4*a02^2*a20^2 + 164*a00^4*a02^2*a22^2 + 
	168*a00^4*a02*a20^2*a22 + 40*a00^4*a02*a22^3 + 70*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	6*a00^4*a22^4 + 40*a00^3*a02^4*a20 + 352*a00^3*a02^3*a20*a22 - 16*a00^3*a02^2*a20^3 + 
	240*a00^3*a02^2*a20*a22^2 - 96*a00^3*a02*a20^3*a22 + 352*a00^3*a02*a20*a22^3 - 
	56*a00^3*a20^5 - 16*a00^3*a20^3*a22^2 + 40*a00^3*a20*a22^4 + 4*a00^2*a02^6 + 
	72*a00^2*a02^5*a22 + 164*a00^2*a02^4*a20^2 - 68*a00^2*a02^4*a22^2 + 
	240*a00^2*a02^3*a20^2*a22 - 16*a00^2*a02^3*a22^3 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 + 168*a00^2*a02*a20^4*a22 + 
	240*a00^2*a02*a20^2*a22^3 + 72*a00^2*a02*a22^5 + 28*a00^2*a20^6 - 68*a00^2*a20^4*a22^2 +
	164*a00^2*a20^2*a22^4 + 4*a00^2*a22^6 - 40*a00*a02^6*a20 - 80*a00*a02^5*a20*a22 + 
	40*a00*a02^4*a20^3 + 168*a00*a02^4*a20*a22^2 + 352*a00*a02^3*a20^3*a22 - 
	96*a00*a02^3*a20*a22^3 + 72*a00*a02^2*a20^5 + 240*a00*a02^2*a20^3*a22^2 + 
	168*a00*a02^2*a20*a22^4 - 80*a00*a02*a20^5*a22 + 352*a00*a02*a20^3*a22^3 - 
	80*a00*a02*a20*a22^5 - 8*a00*a20^7 + 72*a00*a20^5*a22^2 + 40*a00*a20^3*a22^4 - 
	40*a00*a20*a22^6 + a02^8 - 8*a02^7*a22 + 4*a02^6*a20^2 + 28*a02^6*a22^2 + 
	72*a02^5*a20^2*a22 - 56*a02^5*a22^3 + 6*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	70*a02^4*a22^4 + 40*a02^3*a20^4*a22 - 16*a02^3*a20^2*a22^3 - 56*a02^3*a22^5 + 
	4*a02^2*a20^6 + 164*a02^2*a20^4*a22^2 - 68*a02^2*a20^2*a22^4 + 28*a02^2*a22^6 - 
	40*a02*a20^6*a22 + 40*a02*a20^4*a22^3 + 72*a02*a20^2*a22^5 - 8*a02*a22^7 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	a00^8 + 8*a00^7*a20 + 4*a00^6*a02^2 + 40*a00^6*a02*a22 + 28*a00^6*a20^2 + 4*a00^6*a22^2 - 
	72*a00^5*a02^2*a20 - 80*a00^5*a02*a20*a22 + 56*a00^5*a20^3 - 72*a00^5*a20*a22^2 + 
	6*a00^4*a02^4 - 40*a00^4*a02^3*a22 - 68*a00^4*a02^2*a20^2 + 164*a00^4*a02^2*a22^2 - 
	168*a00^4*a02*a20^2*a22 - 40*a00^4*a02*a22^3 + 70*a00^4*a20^4 - 68*a00^4*a20^2*a22^2 + 
	6*a00^4*a22^4 - 40*a00^3*a02^4*a20 + 352*a00^3*a02^3*a20*a22 + 16*a00^3*a02^2*a20^3 - 
	240*a00^3*a02^2*a20*a22^2 - 96*a00^3*a02*a20^3*a22 + 352*a00^3*a02*a20*a22^3 + 
	56*a00^3*a20^5 + 16*a00^3*a20^3*a22^2 - 40*a00^3*a20*a22^4 + 4*a00^2*a02^6 - 
	72*a00^2*a02^5*a22 + 164*a00^2*a02^4*a20^2 - 68*a00^2*a02^4*a22^2 - 
	240*a00^2*a02^3*a20^2*a22 + 16*a00^2*a02^3*a22^3 - 68*a00^2*a02^2*a20^4 + 
	728*a00^2*a02^2*a20^2*a22^2 - 68*a00^2*a02^2*a22^4 - 168*a00^2*a02*a20^4*a22 - 
	240*a00^2*a02*a20^2*a22^3 - 72*a00^2*a02*a22^5 + 28*a00^2*a20^6 - 68*a00^2*a20^4*a22^2 +
	164*a00^2*a20^2*a22^4 + 4*a00^2*a22^6 + 40*a00*a02^6*a20 - 80*a00*a02^5*a20*a22 - 
	40*a00*a02^4*a20^3 - 168*a00*a02^4*a20*a22^2 + 352*a00*a02^3*a20^3*a22 - 
	96*a00*a02^3*a20*a22^3 - 72*a00*a02^2*a20^5 - 240*a00*a02^2*a20^3*a22^2 - 
	168*a00*a02^2*a20*a22^4 - 80*a00*a02*a20^5*a22 + 352*a00*a02*a20^3*a22^3 - 
	80*a00*a02*a20*a22^5 + 8*a00*a20^7 - 72*a00*a20^5*a22^2 - 40*a00*a20^3*a22^4 + 
	40*a00*a20*a22^6 + a02^8 + 8*a02^7*a22 + 4*a02^6*a20^2 + 28*a02^6*a22^2 - 
	72*a02^5*a20^2*a22 + 56*a02^5*a22^3 + 6*a02^4*a20^4 - 68*a02^4*a20^2*a22^2 + 
	70*a02^4*a22^4 - 40*a02^3*a20^4*a22 + 16*a02^3*a20^2*a22^3 + 56*a02^3*a22^5 + 
	4*a02^2*a20^6 + 164*a02^2*a20^4*a22^2 - 68*a02^2*a20^2*a22^4 + 28*a02^2*a22^6 + 
	40*a02*a20^6*a22 - 40*a02*a20^4*a22^3 - 72*a02*a20^2*a22^5 + 8*a02*a22^7 + a20^8 + 
	4*a20^6*a22^2 + 6*a20^4*a22^4 + 4*a20^2*a22^6 + a22^8,
	4*a00^2*a02*a20 - 4*a00^2*a22^2 - a02^4 - 2*a02^2*a20^2 + 4*a02*a20*a22^2 - a20^4,
	4*a00^2*a02*a20 + 4*a00^2*a22^2 + a02^4 + 2*a02^2*a20^2 + 4*a02*a20*a22^2 + a20^4,
	a00^4 + 2*a00^2*a22^2 - 4*a00*a02^2*a22 - 4*a00*a20^2*a22 + 4*a02^2*a20^2 + a22^4,
	a00^4 + 2*a00^2*a22^2 + 4*a00*a02^2*a22 + 4*a00*a20^2*a22 + 4*a02^2*a20^2 + a22^4,
	16*a00^4*a02^2*a20^2 + 16*a00^4*a22^4 - 8*a00^2*a02^4*a22^2 - 16*a00^2*a02^2*a20^2*a22^2 - 
	8*a00^2*a20^4*a22^2 + a02^8 - 4*a02^6*a20^2 + 6*a02^4*a20^4 - 4*a02^2*a20^6 + 
	16*a02^2*a20^2*a22^4 + a20^8,
	a00^8 - 4*a00^6*a22^2 - 8*a00^4*a02^2*a20^2 + 6*a00^4*a22^4 + 16*a00^2*a02^4*a22^2 - 
	16*a00^2*a02^2*a20^2*a22^2 + 16*a00^2*a20^4*a22^2 - 4*a00^2*a22^6 + 16*a02^4*a20^4 - 
	8*a02^2*a20^2*a22^4 + a22^8
	@};
end function;
