//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic '*'(c::RngElt,S::SeqEnum[RngElt]) -> SeqEnum
    {The scalar product [ c*f : f in S ].}
    return [ c*f : f in S ];
end intrinsic;
