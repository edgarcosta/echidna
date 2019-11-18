//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                    QUATERNION ISOGENY CLASSES                            //
//  Copyright (C) 2002 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

//////////////////////////////////////////////////////////////////////////////
//                          Attribute declarations                          //
//////////////////////////////////////////////////////////////////////////////

declare type SymAlgQuat;

declare attributes SymAlgQuat:
    QuaternionOrder;

//////////////////////////////////////////////////////////////////////////////
//                  Canonical Quaternion Representation                     //
//////////////////////////////////////////////////////////////////////////////

function ReducedOrder(A);
    K := QuaternionAlgebra(A);
    return QuaternionOrder([ K!x : x in ReducedBasis(A) ]);
end function;

//////////////////////////////////////////////////////////////////////////////
//                           Creation Function                              //
//////////////////////////////////////////////////////////////////////////////

intrinsic QuaternionIdealClasses(D::RngIntElt,m::RngIntElt :
    Reduce := false) -> SymAlgQuat
    {The set of left ideal classes for a quaternion order of conductor
    m in the quaternion algebra over Q of discriminant D.}
    Q := QuaternionIdealClasses(QuaternionOrder(D,m));
    if Reduce then
	I := LeftIdealClass(Q,1);
	A := LeftOrder(I);
	B := RightOrder(I);
	I := Conjugate(I);
	Bases := [ ];
	for ABasis in A`LeftIdealBases do
	    J := lideal< A | [ A!M[i] : i in [1..4] ] >
		where M := UpperTriangularMatrix(ABasis);
	    K := ReducedLeftIdealClass(I*J);
	    M := HermiteForm(Matrix([ Eltseq(B!x) : x in ReducedBasis(K) ]));
	    Append(~Bases,Eltseq(M)[[1,2,3,4,6,7,8,11,12,16]]);
	end for;
	B`LeftIdealBases := Bases;
	Q := QuaternionIdealClasses(B);
    end if;
    return Q;
end intrinsic;

intrinsic QuaternionIdealClasses(A::AlgQuatOrd :
    Reduce := false) -> SymAlgQuat
    {The set of left ideal classes for the quaternion order A
    in a quaternion algebra over Q.}
    require BaseRing(A) cmpeq Integers() :
	"Argument must be an order in a quatenrion algebra over Q.";
    if not assigned A`LeftIdealBases then
	_ := LeftIdealClasses(A : Reduce := Reduce);
    end if;
    G := New(SymAlgQuat);
    G`QuaternionOrder := A;
    return G;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                               Printing                                   //
//////////////////////////////////////////////////////////////////////////////

intrinsic Print(G::SymAlgQuat,L::MonStgElt)
    {}
    A := G`QuaternionOrder;
    printf "Left ideal classes of quaternion order of level (%o,%o)",
	Discriminant(A) div m, m where m := Level(A);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                     Algebra, Order and Ideal Access                      //
//////////////////////////////////////////////////////////////////////////////

intrinsic RightOrder(G::SymAlgQuat,k::RngIntElt) -> AlgQuatOrd
    {The right order of the kth left ideal class.}
    require k in [1..ClassNumber(G)] :
	"Argument 2 specifies an invalid index.";
    return RightOrder(LeftIdealClass(G,k));
end intrinsic;

intrinsic RightOrders(G::SymAlgQuat) -> SeqEnum
    {The sequence of h right orders of the left ideal classes
    in G, where h is the left ideal class number.} 
    return [ RightOrder(G,k) : k in [1..ClassNumber(G)] ];
end intrinsic;

intrinsic LeftIdealClass(G::SymAlgQuat,k::RngIntElt) -> AlgQuatOrd
    {The left ideal class.}
    h := ClassNumber(G);
    require 1 le k and k le h : "Argument 2 is not a valid index.";
    A := G`QuaternionOrder;
    M := UpperTriangularMatrix(A`LeftIdealBases[k]);
    return I where I := lideal< A | [ A!Eltseq(M[i]) : i in [1..4] ] >;
end intrinsic;

intrinsic LeftIdealClasses(G::SymAlgQuat) -> SeqEnum
    {The sequence of left ideal classes.}  
    A := G`QuaternionOrder;
    return LeftIdealClasses(A);
end intrinsic;

intrinsic IdealClass(G::SymAlgQuat,I::[RngIntElt]) -> AlgQuatOrd
    {An ideal class...}
    require #I eq 2 : "Argument 2 must consist of 2 elements."; 
    h := ClassNumber(G); 
    i, j := Explode(I);
    require 1 le j and j le h : "Argument 2 is not a valid index.";
    J := LeftIdealClass(G,j);
    require 1 le i and i le h : "Argument 2 is not a valid index.";
    I := LeftIdealClass(G,i);
    return Conjugate(I)*J;
end intrinsic;

intrinsic ReducedNormGram(G::SymAlgQuat,I::[RngIntElt]) -> AlgQuatOrd
    {The gram matrix of the norm form of divided by 1/N(I),
    with respect to the reduced basis of I.}
    require #I eq 2 : "Argument 2 must consist of 2 elements."; 
    h := ClassNumber(G); 
    i, j := Explode(I);
    require 1 le j and j le h : "Argument 2 is not a valid index.";
    J := LeftIdealClass(G,j);
    require 1 le i and i le h : "Argument 2 is not a valid index.";
    I := LeftIdealClass(G,i);
    Iij := Conjugate(I)*J;
    return (1/Norm(Iij))*ReducedGramMatrix(Iij);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                        Ideal Class Degeneracies                          //
//////////////////////////////////////////////////////////////////////////////

/*
intrinsic LeftIdealClassDegeneracies(
    H::SymAlgQuat,G::SymAlgQuat) -> SeqEnum
    {The sequence of left ideal classes.}  
    A := Order(H); B := Order(G);
    require B subset A : 
	"Argument 1 must be a defined with respect to " * 
	"a suborder of argument 2.";
    return LeftIdealClassDegeneracies(A,B);
end intrinsic;
*/

//////////////////////////////////////////////////////////////////////////////
//                        Other Access Functions                            //
//////////////////////////////////////////////////////////////////////////////

intrinsic ClassNumber(G::SymAlgQuat) -> RngIntElt
    {}  
    return #(G`QuaternionOrder)`LeftIdealBases;
end intrinsic;

intrinsic Discriminant(G::SymAlgQuat) -> RngIntElt
    {}  
    return Discriminant(G`QuaternionOrder);
end intrinsic;

intrinsic Level(G::SymAlgQuat) -> RngIntElt
    {}  
    return Level(G`QuaternionOrder);
end intrinsic;

intrinsic LevelIndices(G::SymAlgQuat) -> RngIntElt
    {}
    return LevelIndices(G`QuaternionOrder);
end intrinsic;

intrinsic FullLevelIndex(G::SymAlgQuat) -> RngIntElt
    {}  
    return FullLevelIndex(G`QuaternionOrder);
end intrinsic;

intrinsic Order(G::SymAlgQuat) -> RngIntElt
    {}  
    return G`QuaternionOrder;
end intrinsic;

intrinsic RamifiedPrimes(G::SymAlgQuat) -> RngIntElt
    {}  
    return RamifiedPrimes(QuaternionAlgebra(G`QuaternionOrder));
end intrinsic;


