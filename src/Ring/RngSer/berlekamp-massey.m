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

intrinsic BerlekampMassey(S::RngSerPowElt : Precision := 0) -> RngUPolElt
    {}
    FF := BaseRing(Parent(S));
    require IsField(FF) :
	"Argument 1 must be in a power series ring over a field.";
    if Precision eq 0 then
	N := AbsolutePrecision(S);
	require Type(N) eq RngIntElt :
	    "Argument 1 must have finite precision or nonzero Precision specified.";
    else
	N := Precision;
	require AbsolutePrecision(S) ge N :
	    "Argument 1 must have at least precision Precision.";
    end if;
    PF := PolynomialRing(FF); x := PF.1;
    C := PF!1;
    B := PF!1;
    L := 0;
    m := 1;
    b := FF!1;
    for n in [0..N-1] do
	d := &+[ FF | Coefficient(C,i) * Coefficient(S,n-i) : i in [1..L] ];
	d +:= Coefficient(S,n);
	if d eq 0 then
	    m := m + 1;
	elif (2 * L) le n then
	    T := C;
	    C +:= -d/b*x^m*B;
	    L := n + 1 - L;
	    B := T;
	    b := d;
	    m := 1;
	else
	    C +:= -d/b*x^m*B;
	    m +:= 1;
	end if;
    end for;
    return C, L;
end intrinsic;
