////////////////////////////////////////////////////////////////////
//                                                                //  
//                 Extensions to Linear Algebra                   // 
//                         David Kohel                            // 
//                                                                // 
////////////////////////////////////////////////////////////////////

intrinsic CharacteristicPolynomial(T::AlgMatElt,V::ModTupFld
    : Proof := true) -> RngUPolElt
    {Returns the characteristic polynomial of T on V.}
    require Degree(Parent(T)) eq Degree(V) : 
	"Arguments have incompatible degrees";
    n := Dimension(V);
    if n eq Degree(V) then
	return CharacteristicPolynomial(T : Al := "Modular", Proof := Proof);
    end if;
    V := sub< RSpace(BaseRing(V),Degree(V)) | Basis(V) >;
    S := MatrixAlgebra(BaseRing(V),n)!
	&cat[ Coordinates(V,x*T) : x in Basis(V) ];
    return CharacteristicPolynomial(S : Al := "Modular", Proof := Proof);
end intrinsic;

intrinsic CharacteristicPolynomial(T::AlgMatElt,V::ModTupRng
    : Proof := true) -> RngUPolElt
    {Returns the characteristic polynomial of T on V.}
    require Degree(Parent(T)) eq Degree(V) : 
	"Arguments have incompatible degrees";
    n := Dimension(V);
    if n eq Degree(V) then
	return CharacteristicPolynomial(T : Al := "Modular", Proof := Proof);
    end if;
    V := sub< RSpace(BaseRing(V),Degree(V)) | Basis(V) >;
    S := MatrixAlgebra(BaseRing(V),n)!
	&cat[ Coordinates(V,x*T) : x in Basis(V) ];
    return CharacteristicPolynomial(S : Al := "Modular", Proof := Proof  );
end intrinsic;

intrinsic MinimalPolynomial(T::AlgMatElt,V::ModTupFld
    : Proof := true) -> RngUPolElt
    {Returns the minimal polynomial of T on V.}
    require Degree(Parent(T)) eq Degree(V) : 
	"Arguments have incompatible degrees";
    n := Dimension(V);
    if n eq Degree(V) then
	return MinimalPolynomial(T : Al := "Modular", Proof := Proof);
    end if;
    V := sub< RSpace(BaseRing(V),Degree(V)) | Basis(V) >;
    S := MatrixAlgebra(BaseRing(V),n)!
	&cat[ Coordinates(V,x*T) : x in Basis(V) ];
    return MinimalPolynomial(S : Al := "Modular", Proof := Proof);
end intrinsic;

intrinsic CharacteristicPolynomial(T::AlgMatElt,L::Lat
    : Proof := true ) -> RngUPolElt
    {Returns the characteristic polynomial of T on L.}
    require Degree(Parent(T)) eq Degree(L) : 
	"Arguments have incompatible degrees";
    n := Rank(L);
    if n eq Degree(L) then
	return CharacteristicPolynomial(T : Al := "Modular", Proof := Proof);
    end if;
    S := MatrixAlgebra(Integers(),n)!
	&cat[ Coordinates(L,x*T) : x in Basis(L) ];
    return CharacteristicPolynomial(S : Al := "Modular", Proof := Proof);
end intrinsic;

intrinsic MinimalPolynomial(T::AlgMatElt,L::Lat 
    : Proof := true) -> RngUPolElt
    {Returns the minimal polynomial of T on V.}
    require Degree(Parent(T)) eq Degree(L) : 
	"Arguments have incompatible degrees";
    n := Rank(L);
    if n eq Degree(L) then
	return MinimalPolynomial(T : Al := "Modular", Proof := Proof);
    end if;
    S := MatrixAlgebra(Integers(),n)!
	&cat[ Coordinates(L,x*T) : x in Basis(L) ];
    return MinimalPolynomial(S : Al := "Modular", Proof := Proof);
end intrinsic;

intrinsic Trace(T::AlgMatElt,V::ModTupFld) -> RngElt
    {The trace of T on V.}
    return &+[ Coordinates(V,V.i*T)[i] : i in [1..Dimension(V)] ];
end intrinsic;

intrinsic Determinant(T::AlgMatElt,V::ModTupFld) -> RngElt
    {The determinant of T on V.}
    return Determinant(MatrixAlgebra(BaseRing(V),Dimension(V))!
	&cat[ Coordinates(V,v*T) : v in Basis(V) ]);
end intrinsic;

intrinsic Eigenvalues(T::AlgMatElt,V::ModTupFld) -> RngElt
    {Returns the eigenvalues of T on V.}
    N := MatrixAlgebra(BaseRing(V),Dimension(V))!
	&cat[ Coordinates(V,v*T) : v in Basis(V) ];
    return Eigenvalues(N);
end intrinsic;

