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

/* Not much to implement, just preserving a common syntax for CM fields. */

intrinsic IsQuadraticCMField(K::FldNum) -> BoolElt
    {}
    return Degree(K) eq 2 and IsCMField(K);
end intrinsic;

intrinsic QuadraticCMFieldInvariants(K::FldNum) -> BoolElt
    {}
    require IsQuadraticCMField(K) : "Argument must be a quadratic CM field.";
    return [ Discriminant(MaximalOrder(K)) ];
end intrinsic;

