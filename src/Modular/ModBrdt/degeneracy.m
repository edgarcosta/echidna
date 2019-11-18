intrinsic DegeneracyMaps(Q::SymAlgQuat,p::RngIntElt)
    -> AlgMatElt, SeqEnum, SeqEnum
    {}
    N, m, c := Explode(LevelIndices(Q));
    D := N div (m*c^3); assert c eq 1;
    require m mod p eq 0 : 
        "Argument 2 must divide the conductor of argument 1.";
    return DegeneracyMaps(Order(Q),p);
end intrinsic;

intrinsic DegeneracyMaps(A::AlgQuatOrd,p::RngIntElt)
    -> AlgMatElt, SeqEnum, SeqEnum
    {}
    N, m, c := Explode(LevelIndices(A));
    D := N div (m*c^3); assert c eq 1;
    require m mod p eq 0 : 
        "Argument 2 must divide the conductor of argument 1.";
    S0 := SuperOrders(A,p);
    assert #S0 eq 1 or &meet S0 eq A;
    degen_maps := [];
    degen_idxs := [];
    degen_isom := [];
    DBQA := QuaternionAlgebraDatabase();
    K1 := QuaternionAlgebra(A);
    Q0 := QuaternionIdealClasses(DBQA,D,m div p);
    vprintf Brandt :
	"  Computing degeneracy (%o,%o) -> (%o,%o)\n", D, m, D, m div p;
    vprint Brandt : "  Degeneracy ideal class number:", ClassNumber(Q0);
    tyme := Cputime();
    K0 := QuaternionAlgebra(Order(Q0));
    vprint Brandt, 2 : "  Finding quaternion algebra isomorphism.";
    _, hK := IsIsomorphic(K1,K0 : Isomorphism);
    vprint Brandt :
	"  Found quaternion algebra isomorphism:", Cputime(tyme);
    B0 := QuaternionOrder([ hK(x) : x in Basis(S0[1]) ]);
    pis := [];
    i := 0;
    tyme := Cputime();
    repeat
	i +:= 1;
	bool, hB := IsIsomorphic(RightOrder(Q0,i),B0);
    until bool;
    vprint Brandt :
	"  Found quaternion order isomorphism:", Cputime(tyme);
    tyme := Cputime();
    Bases := [];
    Bi := Domain(hB);
    Ji := Conjugate(LeftIdealClass(Q0,i));
    for J in LeftIdealClasses(Q0) do
	M := HermiteForm(Matrix([
	    Eltseq(S0[1]!(K0!(B0!hB(Bi!x)))@@hK) : x in Basis(Ji*J) ]));
	Append(~Bases,Eltseq(M)[[1,2,3,4,6,7,8,11,12,16]]); 
    end for;
    S0[1]`LeftIdealBases := Bases;
    IdlsA := LeftIdealClasses(A); 
    vprint Brandt :
	"  Found left ideal class mapping:", Cputime(tyme);
    tyme := Cputime();
    rho, idx := LeftIdealClassDegeneracies(S0[1],IdlsA);
    inc := Matrix([ Eltseq(x@hK@@hB) : x in Basis(A) ]);
    Append(~degen_maps,rho);
    Append(~degen_idxs,idx);
    Append(~degen_isom,inc);
    if #S0 eq 2 then 
	tyme := Cputime();
	vprint Brandt :
	    "  Determined first degeneracies:", Cputime(tyme);
	q := p^Valuation(m,p);
	I0 := lideal< S0[1] | Basis(CommutatorIdeal(A) + ideal<A|q>) >;
	assert RightOrder(I0) eq S0[2];
	IdlsA := [ lideal< S0[1] |
	    [ x*y : x in Basis(I0), y in Basis(I) ] > : I in IdlsA ];
	rho, idx := LeftIdealClassDegeneracies(S0[1],IdlsA);
	inc := Matrix([ Eltseq(x@hK@@hB) : x in Basis(A) ]);
	Append(~degen_maps,rho);
	Append(~degen_idxs,idx);
	Append(~degen_isom,inc);
	vprint Brandt :
	    "  Determined second degeneracies:", Cputime(tyme);
    end if;
    return degen_maps, degen_idxs, degen_isom;
end intrinsic;

intrinsic DegeneracyMaps(M::ModBrdt,p::RngIntElt) -> AlgMatElt, SeqEnum
    {}
    N, m, c := Explode(LevelIndices(M));
    D := N div (m*c^3); assert c eq 1;
    require m mod p eq 0 : 
        "Argument 2 must divide the conductor of argument 1.";
    require assigned M`LeftIdeals : 
        "Left ideals of argument 1 must be defined.";
    A := LeftOrder(M`LeftIdeals[1]);
    assert assigned A`LeftIdealBases;
    return DegeneracyMaps(A,p);
end intrinsic;
