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

function SatakeHumbertPolynomial04(R)
    P<s2,s3,s5,s6> := PolynomialRing(R,4); 
    return -1433272320000*s6^5 + 1672151040000*s6^4*s3^2 + 487710720000*s6^4*s2^3 + 
        716636160000*s6^3*s5^2*s2 - 692748288000*s6^3*s5*s3*s2^2 - 
        756449280000*s6^3*s3^4 - 273715200000*s6^3*s3^2*s2^3 - 66216960000*s6^3*s2^6
        - 477757440000*s6^2*s5^3*s3 + 71663616000*s6^2*s5^2*s3^2*s2 - 
        149100134400*s6^2*s5^2*s2^4 + 236888064000*s6^2*s5*s3^3*s2^2 + 
        142166016000*s6^2*s5*s3*s2^5 + 165888000000*s6^2*s3^6 + 
        68567040000*s6^2*s3^4*s2^3 + 9711360000*s6^2*s3^2*s2^6 + 
        4484160000*s6^2*s2^9 - 65691648000*s6*s5^4*s2^2 + 302579712000*s6*s5^3*s3^3 
        + 214592716800*s6*s5^3*s3*s2^3 - 248433868800*s6*s5^2*s3^4*s2 - 
        131598950400*s6*s5^2*s3^2*s2^4 + 10338969600*s6*s5^2*s2^7 + 
        41472000000*s6*s5*s3^5*s2^2 + 10934784000*s6*s5*s3^3*s2^5 - 
        9735552000*s6*s5*s3*s2^8 - 17694720000*s6*s3^8 - 16957440000*s6*s3^6*s2^3 - 
        4554720000*s6*s3^4*s2^6 + 378000000*s6*s3^2*s2^9 - 151470000*s6*s2^12 - 
        47775744000*s5^6 + 191102976000*s5^5*s3*s2 - 291432038400*s5^4*s3^2*s2^2 + 
        4201279488*s5^4*s2^5 - 48625090560*s5^3*s3^5 + 198499368960*s5^3*s3^3*s2^3 -
        11784683520*s5^3*s3*s2^6 + 50429952000*s5^2*s3^6*s2 - 
        69312153600*s5^2*s3^4*s2^4 + 8127475200*s5^2*s3^2*s2^7 - 
        238723200*s5^2*s2^10 - 16257024000*s5*s3^7*s2^2 + 13999104000*s5*s3^5*s2^5 -
        1664064000*s5*s3^3*s2^8 + 222264000*s5*s3*s2^11 + 737280000*s3^10 + 
        2641920000*s3^8*s2^3 - 863840000*s3^6*s2^6 + 207270000*s3^4*s2^9 - 
        20250000*s3^2*s2^12 + 2041875*s2^15;
end function;