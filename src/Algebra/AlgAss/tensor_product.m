////////////////////////////////////////////////////////////////////////
//                                                                    //
//                ASSOCIATIVE ALGEBRA TENSOR PRODUCTS                 //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic MyTensorProduct(A::AlgMat,B::AlgMat) -> AlgMat, Map, Map
    {The tensor product T of A and B, followed by the inclusion 
    maps A->T and B->T.}
    // N.B. Tensor product of matrix algebras exists but the inclusion
    // maps are not returned.
    AB := TensorProduct(A,B);
    return AB, mA, mB
	where mA := hom< A->AB | x :-> TensorProduct(x,B!1) >
	where mB := hom< B->AB | x :-> TensorProduct(A!1,x) >;
end intrinsic;

intrinsic TensorProduct(A::AlgAss,B::AlgAss) -> AlgAss, Map, Map
    {The tensor product T of A and B, followed by the inclusion 
    maps A->T and B->T.}
    K := BaseRing(A);
    require BaseRing(B) cmpeq K : 
	"Arguments must be defined over the same base ring.";
    require 1 in A and 1 in B :	"Arguments must be unitary algebras.";
    MA := [ LeftMultiplicationMatrix(x) : x in Basis(A) ];
    MB := [ LeftMultiplicationMatrix(x) : x in Basis(B) ];
    AB := AssociativeAlgebra< K, #MA*#MB |
	&cat[ Eltseq(TensorProduct(X,Y)) : Y in MB, X in MA ]>;
    Alg2Vect := func< x | Vector(Eltseq(x)) >;
    mA := hom< A->AB | x :->
	AB!Eltseq(TensorProduct(Alg2Vect(x),Alg2Vect(B!1))) >;
    mB := hom< B->AB | y :->
	AB!Eltseq(TensorProduct(Alg2Vect(A!1),Alg2Vect(y))) >;
    return AB, mA, mB;
end intrinsic;

intrinsic ReducedTensorPower(A::AlgAss,n::RngIntElt) -> AlgAss
    {The Brouer class of the n-th tensor product of A with itself,
    reduced by the degree of a splitting field.}
    K := BaseRing(A);
    require 1 in A : "Argument must be a unitary algebra.";
    require n eq 2 : "Argument 2 must be 2.";
    MA := [ LeftMultiplicationMatrix(x) : x in Basis(A) ];
    AA := AssociativeAlgebra< K, #MA^2 | &cat[
	Eltseq(TensorProduct(X,Y)) : X, Y in MA ] : Check := false >;
    Alg2Vect := func< x | Vector(Eltseq(x)) >;
    m1 := hom< A->AA | x :->
	AA!Eltseq(TensorProduct(Alg2Vect(x),Alg2Vect(A!1))) >;
    m2 := hom< A->AA | x :->
	AA!Eltseq(TensorProduct(Alg2Vect(A!1),Alg2Vect(x))) >;
    x := PrimitiveElement(SplittingField(A));
    P := PolynomialRing(AA); X := P.1;
    e := Evaluate(F div (X-m2(x)),m1(x)) * Evaluate(G,m1(x))^-1
	where G := Derivative(F) where F := P!MinimalPolynomial(x);
    BB := sub< AA | [ e*x*e : x in Basis(AA) ] >; 
    return BB;
end intrinsic;

