intrinsic MatrixMinor(M::ModMatRngElt,I1::[RngIntElt],I2::[RngIntElt])
    -> ModMatRngElt
    {Returns the submatrix of coordinates (i,j) in I1 x I2.}
    R := BaseRing(Parent(M));
    return RMatrixSpace(R,#I1,#I2)!
	&cat[ [ M[i,j] : j in I2 ] : i in I1 ];
end intrinsic;

intrinsic MatrixMinor(M::AlgMatElt,I1::[RngIntElt],I2::[RngIntElt])
    -> AlgMatElt
    {Returns the submatrix of coordinates (i,j) in I1 x I2.}
    R := BaseRing(Parent(M));
    return RMatrixSpace(R,#I1,#I2)!
	&cat[ [ M[i,j] : j in I2 ] : i in I1 ];
end intrinsic;
