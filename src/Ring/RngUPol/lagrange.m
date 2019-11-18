//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//         Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu.au>         //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic LagrangeInterpolation(
    X::SeqEnum[RngElt],Y::SeqEnum[RngElt]) -> RngUPolElt
    {Given X = [x0,..,xn] a sequence of ring elements and Y = [y0,..,yn] a 
    sequence of values of a function in the ring, returns the unique polynomial
    of degree (up to) n which interpolates these values.}
    /*
    Set fi = \prod_{j \ne i} (x-xj)/(xi-xj), and f = \sum_{i} yi fi.
    */
    n := #X; R := Universe(Y);
    bool, X := CanChangeUniverse(X,R);
    require n eq #Y and bool :
	"Arguments must be nonempty sequences of the same length over the same ring.";
    P := PolynomialRing(R); x := P.1;
    return &+[ &*[ (x-X[j])/(X[i]-X[j]) : j in [1..n] | j ne i ] * Y[i] : i in [1..n] ];
end intrinsic;
