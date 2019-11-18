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

intrinsic '+'(P::Pt,Q::Pt) -> Pt
    {}
    C := Scheme(P);
    require ISA(Type(C),Crv) : "Addition law not defined on this scheme (not curve).";
    require assigned C`AdditionMorphism: "Addition morphism not defined on this curve.";
    return C`AdditionMorphism(Eltseq(P) cat Eltseq(Q));
end intrinsic;

intrinsic '-'(P::Pt) -> Pt
    {}
    C := Scheme(P);
    require ISA(Type(C),Crv) : "Addition law not defined on this scheme (not curve).";
    require assigned C`InverseMorphism: "Inverse law not defined on this curve.";
    return C`InverseMorphism(P);
end intrinsic;

intrinsic '-'(P::Pt,Q::Pt) -> Pt
    {}
    C := Scheme(P);
    require ISA(Type(C),Crv) : "Addition law not defined on this scheme (not curve).";
    require assigned C`InverseMorphism: "Inverse law not defined on this curve.";
    require assigned C`AdditionMorphism: "Addition law not defined on this curve.";
    return C`AdditionMorphism(Eltseq(P) cat Eltseq(C`InverseMorphism(Q)));
end intrinsic;

intrinsic '*'(n::RngIntElt,P::Pt) -> Pt
    {}
    C := Scheme(P);
    require ISA(Type(C),Crv) : "Addition law not defined on this scheme (not curve).";
    require assigned C`InverseMorphism: "Inverse law not defined on this curve.";
    require assigned C`AdditionMorphism: "Addition law not defined on this curve.";
    if n lt 0 then
	return -n * (-P);
    elif n eq 0 then
	return Parent(P)!Identity(C);
    elif n eq 1 then
	return P;
    elif n eq 2 then
	return C`AdditionMorphism(Eltseq(P) cat Eltseq(P));
    end if;
    R := Parent(P)!Identity(C);
    Q := P;
    plus := C`AdditionMorphism;
    bits := IntegerToSequence(n,2);
    for i in [1..#bits-1] do
	if bits[i] eq 1 then
	    R := plus(Eltseq(R) cat Eltseq(Q));
	end if;
	Q := plus(Eltseq(Q) cat Eltseq(Q));
    end for;
    if bits[#bits] eq 1 then
	R := plus(Eltseq(R) cat Eltseq(Q));
    end if;
    return R;
end intrinsic;
