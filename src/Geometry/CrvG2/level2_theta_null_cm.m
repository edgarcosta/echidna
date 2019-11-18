//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

/*
> K := QuarticCMField([ 5, 33, 241 ]);
> OK := MaximalOrder(K);
> XX := ThetaNullValues(OK,128);
> TT := [ Level2ThetaNullPointToRosenhainInvariants(xx) : xx in XX ];
> JJ := [ RosenhainToAbsoluteIgusaInvariants(tt) : tt in TT ];

*/

intrinsic ThetaNullValues(OK::RngOrd,prec::RngIntElt) -> SeqEnum
    {}
    // char should be a (2g)x1 matrix: the characteristic
    // z    should be a gx1 matrix: the argument in C^g
    // tau  should be an element of g-dimensional Siegel upper half space 
    //      (symmetric gxg complex matrix with positive definite imaginary part)
    CC := ComplexField(prec);
    lattices := [];
    G, m := ClassGroup(OK);
    for g in G do
	I := MinkowskiReduction(m(g));
	bool, xi := IsPrincipallyPolarizable(I : Reduction := true);
	if bool then
	    Append(~lattices,SmallPeriodMatrix(I,CC)); // (I,xi,CC));
	end if;
    end for;
    chars := [
	Matrix(CC,1,[0,0,0,0]),
	Matrix(CC,1,[0,1/2,0,0]),
	Matrix(CC,1,[1/2,0,0,0]),
	Matrix(CC,1,[1/2,1/2,0,0]) ];
    zero := Matrix(CC,1,[0,0]);
    return [ [ InternalTheta(char,zero,tau) : char in chars ] : tau in lattices ];
end intrinsic;
