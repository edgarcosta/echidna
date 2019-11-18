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

function SatakeHumbertPolynomial05(R)
    P<s2,s3,s5,s6> := PolynomialRing(R,4); 
    return 518400*s6^2 - 345600*s6*s3^2 - 79200*s6*s2^3 - 248832*s5^2*s2 + 
	138240*s5*s3*s2^2 + 57600*s3^4 + 7200*s3^2*s2^3 + 3025*s2^6;
end function;
