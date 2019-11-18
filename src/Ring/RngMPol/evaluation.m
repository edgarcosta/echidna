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


/*
// Defined in Magma kernel as of V2.14:

intrinsic Evaluate(f::FldFunRatMElt,S::[RngElt]) -> RngElt
    {}
    num := Evaluate(Numerator(f),S);
    den := Evaluate(Denominator(f),S);
    bool, inv := IsInvertible(den);
    require bool :
	"Denominator of argument 1 must evaluate to a unit.";
    return num*inv;
end intrinsic;
*/

intrinsic '@'(S::[RngElt],f::RngMPolElt) -> RngElt
    {}
    require #S eq Rank(Parent(f)) :
	"Argument 1 must have length equal to " *
	"the rank of the parent of argument 2.";
    return Evaluate(f,S);
end intrinsic;

intrinsic '@'(S::[RngElt],f::FldFunRatMElt) -> RngElt
    {}
    require #S eq Rank(Parent(f)) :
	"Argument 1 must have length equal to " *
	"the rank of the parent of argument 2.";
    return Evaluate(f,S);
end intrinsic;

