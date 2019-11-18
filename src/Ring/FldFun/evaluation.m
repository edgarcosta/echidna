//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2006 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//               Generic code for evaluation of polynomials                 //
//////////////////////////////////////////////////////////////////////////////

intrinsic '@'(a::RngElt,f::FldFunRatUElt) -> RngElt
    {}
    return Evaluate(f,a);
end intrinsic;

