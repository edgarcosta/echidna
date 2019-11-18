////////////////////////////////////////////////////////////////////////
//                                                                    //
//                      Attribute Access Functions                    //
//                             David Kohel                            //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic AtkinLehnerPrimes(M::ModBrdt) -> SeqEnum
    {The sequence of primes for which the Atkin-Lehner operator 
    can be computed.}
    if not assigned M`AtkinLehnerPrimes then
        N := Level(M);
        D := Discriminant(M);
        prms := PrimeDivisors(N);
        admit_prms :=
            [ p : p in prms | D mod p ne 0 or Valuation(N,p) le 2 ];
        M`AtkinLehnerPrimes := admit_prms;
    end if;
    return M`AtkinLehnerPrimes;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                       Ambient Module                               //
//       Only certain data will be cached on the ambient module,      //
//       and propagate to the submodules.                             //
////////////////////////////////////////////////////////////////////////

intrinsic AmbientModule(M::ModBrdt) -> ModBrdt
    {}
    if assigned M`AmbientModule then
	return M`AmbientModule;
    end if;
    return M;
end intrinsic;

intrinsic AmbientSpace(M::ModBrdt) -> ModBrdt
    {}
    if assigned M`AmbientModule then
	return M`AmbientModule;
    end if;
    return M;
end intrinsic;

intrinsic LeftIdealClasses(M::ModBrdt) -> SeqEnum
    {}
    A := AmbientModule(M);
    require assigned A`LeftIdeals :
	"Left ideal classes not defined for this argument.";
    return A`LeftIdeals;
end intrinsic;

intrinsic QuaternionOrder(M::ModBrdt) -> SeqEnum
    {}
    A := AmbientModule(M);
    require assigned A`LeftIdeals :
	"Quaternion order not defined for this argument.";
    return LeftOrder(A`LeftIdeals[1]);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                Booleans for Ambient Determination                  //
////////////////////////////////////////////////////////////////////////

intrinsic IsFull(M::ModBrdt) -> BoolElt
    {}
    return M`IsFull;
end intrinsic;

intrinsic IsAmbientModule(M::ModBrdt) -> BoolElt
    {True if only M is equal to AmbientModule(M).}
    return M`IsFull;
end intrinsic;

intrinsic IsAmbientSpace(M::ModBrdt) -> BoolElt
    {True if only M is equal to AmbientModule(M).}
    return M`IsFull;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                     Degree and Dimension                           //
////////////////////////////////////////////////////////////////////////

intrinsic Degree(M::ModBrdt) -> RngIntElt
    {}
    return Dimension(AmbientModule(M));
end intrinsic;

intrinsic Dimension(M::ModBrdt) -> RngIntElt
    {}
    return Dimension(M`Module);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                          Hecke Bound                               //
////////////////////////////////////////////////////////////////////////

intrinsic HeckeBound(M::ModBrdt : AgasheStein := false) -> RngIntElt
    {}
    N := Level(M);
    prms := PrimeDivisors(N);
    if AgasheStein then
	// Bound of Agashe-Stein from Lario-Schoof:
	return (Weight(M) * N * &*[ 1+p : p in prms ]) div 12;
    end if;
    return (Weight(M) * &*[ 1+p : p in prms ]) div 12;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                 Inner Product Module Structure                     //
////////////////////////////////////////////////////////////////////////

intrinsic Norm(x::ModBrdtElt) -> RngElt
    {}
    return Norm(x`Element);
end intrinsic;

intrinsic GramMatrix(M::ModBrdt) -> AlgMatElt
    {}
    return GramMatrix(M`Module); 
end intrinsic;

intrinsic InnerProductMatrix(M::ModBrdt) -> AlgMatElt
    {}
    return InnerProductMatrix(M`Module); 
end intrinsic;

intrinsic InnerProduct(x::ModBrdtElt,y::ModBrdtElt) -> RngElt
    {}
    return InnerProduct(x`Element,y`Element);
end intrinsic;

intrinsic ReducedNormGram(M::ModBrdt,I::[RngIntElt]) -> AlgMatElt
    {The (reduced) norm gram matrix in position (i,j).}
    h := Degree(M);
    if not IsAmbientModule(M) then
	M := AmbientModule(M);
    end if;
    require #I eq 2 : "Argument 2 must have length 2.";
    i, j := Explode(I);
    require 1 le i and i le h and 1 le j and j le h :
	"Invalid range of elements for argument 2.";
    if not assigned M`NormGrams then
	if i eq j then
	    return GramMatrix(RightOrder(M`LeftIdeals[i]));
	else
	    return GramMatrix(
		Conjugate(M`LeftIdeals[i])*M`LeftIdeals[j]);
	end if;
    end if;
    if j lt i then
        k := Binomial(h+1,2) - Binomial(h-j+2,2) + Abs(i-j) + 1;
    else
	k := Binomial(h+1,2) - Binomial(h-i+2,2) + Abs(i-j) + 1;
    end if;
    return M`NormGrams[k];
end intrinsic;

intrinsic DiscriminantForms(M::ModBrdt) -> SeqEnum
    {}
    h := Degree(M);
    Grams := [ ReducedNormGram(M,[i,i]) : i in [1..Degree(M)] ];
    Discs := {@ @};
    I := [];
    for i in [1..h] do
	X := Grams[i];
	D := MinkowskiGramReduction(
	    Matrix(3, [ X[1,1]*X[i,j]-X[1,j]*X[1,i] : 
	    i, j in [2..4] ]) : Canonical);
	k := Index(Discs,D);
	if k eq 0 then
	    Include(~Discs,D);
	end if;
	I[i] := k eq 0 select #Discs else k;
    end for;
    return Discs, I;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                 Inner Product Module Structure                     //
////////////////////////////////////////////////////////////////////////

intrinsic Conductor(M::ModBrdt) -> RngIntElt
    {}
    return M`Conductor;
end intrinsic;

intrinsic Discriminant(M::ModBrdt) -> RngIntElt
    {}
    return &*M`RamifiedPrimes; 
end intrinsic;

intrinsic Level(M::ModBrdt) -> RngIntElt
    {}
    return Discriminant(M)*Conductor(M);
end intrinsic;

intrinsic FullLevelIndex(M::ModBrdt) -> RngIntElt
    {}
    if not assigned M`FullLevelIndex then
	M`FullLevelIndex := 1;
    end if;
    return M`FullLevelIndex;
end intrinsic;

intrinsic LevelIndices(M::ModBrdt) -> RngIntElt
    {}
    D := Discriminant(M);
    m := Conductor(M);
    r := FullLevelIndex(M);
    return [ D*m, m div r^3, r ];
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                           Module                                   //
////////////////////////////////////////////////////////////////////////

intrinsic Lattice(M::ModBrdt) -> ModTupRng
    {}
    return Lattice(L,InnerProductMatrix(L)) where L := M`Module;
end intrinsic;

intrinsic RSpace(M::ModBrdt) -> ModTupRng
    {}
    return M`Module;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                      Base Ring and Basis                           //
////////////////////////////////////////////////////////////////////////

intrinsic BaseRing(M::ModBrdt) -> Rng
    {}
    return M`BaseRing;
end intrinsic;

intrinsic Basis(M::ModBrdt) -> SeqEnum
    {A basis for M.}
    return [ M!x : x in Basis(M`Module) ];
end intrinsic;

intrinsic BaseExtend(M::ModBrdt,R::Rng) -> ModBrdt
    {}
    N := New(ModBrdt);
    N`IsFull := M`IsFull;
    N`RamifiedPrimes := M`RamifiedPrimes;
    N`Conductor := M`Conductor;
    N`BaseRing := R;
    N`Module := ChangeRing(M`Module,R);
    if assigned M`FullLevelIndex then
	N`FullLevelIndex := M`FullLevelIndex;
    end if;
    if M`IsFull then
	N`AutoNums := M`AutoNums;
        N`NormGrams := M`NormGrams;
	N`HeckePrecision := 1;
	N`ThetaSeries := [ PowerSeriesRing(R) | f : f in M`ThetaSeries ];
        N`HeckePrimes := M`HeckePrimes;
        N`HeckeOperators := [
            MatrixAlgebra(R,Dimension(M))!T : T in M`HeckeOperators ];
    else
        N`AmbientModule := BaseExtend(AmbientModule(M),R);
    end if;
    if assigned M`DecompositionIdeal then
	N`DecompositionIdeal := M`DecompositionIdeal;
    else
	N`DecompositionIdeal := {@ @};
    end if;
    return N; 
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                       Coordinate Access                            //
////////////////////////////////////////////////////////////////////////

intrinsic Eltseq(x::ModBrdtElt) -> SeqEnum
    {}
    return Eltseq(x`Element);
end intrinsic;

