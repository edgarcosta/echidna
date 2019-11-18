//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2010 David Kohel <kohel@iml.univ-mrs.fr>           //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BaseRing(I::RngInt) -> RngInt
    {The base ring ZZ of I (caution: ideals in ZZ are also RngInt's.)}
    return IntegerRing();
end intrinsic;

intrinsic Basis(I::RngInt) -> RngInt
    {The basis of I over ZZ (caution: ideals in ZZ are also RngInt's.)}
    return [ Generator(I) ];
end intrinsic;
