//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////


intrinsic Divisors(f:RngUPolElt) -> SeqEnum
    {The sequence of divisors of the polynomial f.}
    facs := Factorization(f);
    exps := CartesianProduct([ [0..f[2]] : f in facs ]);
    return [ &*[ facs[i][1]^e[i] : i in [1..#facs] ] : e in exps ];
end intrinsic;
