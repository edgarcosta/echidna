////////////////////////////////////////////////////////////////////////
//                                                                    //
//                    Brandt Modules of Quaternions                   //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        Accessory Functions                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function PrintPadded(i,r)
    return &cat[ Strings() | "0" : i in [1..r-#s] ] cat s
	where s := Sprint(i);
end function;

function NormGramsOrder(left_ideals);
    auto_nums := [ Integers() | ];
    norm_grams := [ MatrixAlgebra(Integers(),4) | ];
    k := 1;
    h := #left_ideals;
    if GetVerbose("Brandt") ge 2 then
	cols := GetColumns();
	SetColumns(0);
	r := #Sprint(h);
	one := PrintPadded(1,r);
	printf "Computing gram row entries [1-%o]: %o", h, one;
    end if;
    for i in [1..h] do
        norm_grams[k] := ReducedGramMatrix(RightOrder(left_ideals[i]));
        auto_nums[i] :=
            2*#ShortestVectors(LatticeWithGram(norm_grams[k]));
        RI := Conjugate(left_ideals[i]);
        k +:= 1;
        for j in [i+1..h] do
            J := RI*left_ideals[j];
            norm_grams[k] := Norm(J)^-1 * ReducedGramMatrix(J); 
            k +:= 1;
        end for;
	vprintf Brandt, 2 : "\b"^r * PrintPadded(i,r);
    end for;
    if GetVerbose("Brandt") ge 2 then
	SetColumns(cols);
	print "";
    end if;
    return norm_grams, auto_nums;
end function;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Creation functions                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic BrandtModule(D::RngIntElt : ComputeGrams := true) -> ModBrdt
    {}
    prms := PrimeDivisors(D);
    require &*prms eq D and #prms mod 2 eq 1 : 
        "Argument must be a product of an odd number of primes.";
    A := QuaternionOrder(D);
    return BrandtModule(A,Integers() : ComputeGrams := ComputeGrams);
end intrinsic;

intrinsic BrandtModule(D::RngIntElt,m::RngIntElt : 
    ComputeGrams := false) -> ModBrdt
    {}
    prms := PrimeDivisors(D);
    require Max([ Valuation(D,p) : p in prms ]) le 1 :
        "Argument 1 can have valuation at most 1 at each prime.";
    require Max([ Valuation(m,p) : p in prms ]) le 1 :
        "Argument 2 can have valuation at most 1 " * 
        "at each prime divisor of argument 2.";
    A := QuaternionOrder(D,m);
    return BrandtModule(A,Integers() : ComputeGrams := ComputeGrams);
end intrinsic;

intrinsic BrandtModule(A::AlgQuatOrd : ComputeGrams := false) -> ModBrdt
    {}
    return BrandtModule(A,Integers() : ComputeGrams := ComputeGrams);
end intrinsic;

intrinsic BrandtModule(A::AlgQuatOrd,R::Rng : ComputeGrams := false)
    -> ModBrdt
    {The Eichler-Brandt quaternion ideal divisor group.}
    M := New(ModBrdt);
    M`IsFull := true;
    M`RamifiedPrimes := RamifiedPrimes(QuaternionAlgebra(A));
    M`Conductor := Level(A);
    M`FullLevelIndex := LevelIndices(A)[3];
    M`BaseRing := R;
    M`LeftIdeals := LeftIdealClasses(A);
    if ComputeGrams then 
        M`NormGrams, M`AutoNums := NormGramsOrder(M`LeftIdeals);
    else
        M`AutoNums := [ #Units(RightOrder(I)) : I in M`LeftIdeals ];
    end if;
    M`HeckePrecision := 1;
    M`ThetaSeries := [ PowerSeriesRing(R) | ];
    M`HeckePrimes := [ Integers() | ];
    h := #M`AutoNums;
    MatR := MatrixAlgebra(R,h);
    M`HeckeOperators := [ MatR | ];
    M`Module := RSpace(R,h,
        DiagonalMatrix(MatR,[ w div 2 : w in M`AutoNums ]));
    M`DecompositionIdeal := {@ @};
    return M; 
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Coercions                                //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function init_bool_ModBrdtElt(M,v)
    val, u := IsCoercible(M`Module,v);
    if Type(v) ne SeqEnum then v := Eltseq(v); end if;
    if not val then
	dim := Dimension(M);
	if dim eq #v then
	    val := true;
	    u := &+[ v[i]*M`Module.i : i in [1..dim] ];
	else
	    x := "Invalid coercion";
	end if;
    end if;
    if val then
        x := New(ModBrdtElt);
        x`Parent := M;
        x`Element := u;
    end if;
    return val, x;
end function;

intrinsic IsCoercible(M::ModBrdt,s::.) -> BoolElt, ModBrdtElt
    {}
    if Type(s) eq ModBrdtElt then
        N := Parent(s);
        if M eq N then
            return true, s;
        end if;
        A := AmbientModule(M);
        if A eq AmbientModule(N) then
            v := A`Module!s`Element;
            if v in M`Module then
                return init_bool_ModBrdtElt(M,s);
            end if;
        end if;
    elif Type(s) eq ElementType(M`Module) then
        if s in M`Module then
	    return init_bool_ModBrdtElt(M,s);
        end if;
    elif Type(s) eq SeqEnum and #s in [Dimension(M),Degree(M)] then
        R := Universe(s);
        if Type(R) eq RngInt or R eq BaseRing(M) then
	    return init_bool_ModBrdtElt(M,s);
        end if; 
    end if;
    print "Type(s) =", Type(s);
    return false, "Invalid coercion";
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Printing                                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Print(M::ModBrdt, level::MonStgElt)
    {}
    D := Discriminant(M);
    m := Conductor(M);
    printf "Brandt module of level (%o,%o), " *
        "dimension %o, and degree %o over %o", 
        D, m, Dimension(M), Degree(M), BaseRing(M);
end intrinsic;

intrinsic Print(x::ModBrdtElt, level::MonStgElt)
    {}
    printf "%o", x`Element;
end intrinsic;

intrinsic '.'(M::ModBrdt,i::RngIntElt) -> ModBrdtElt
    {}
    require i in [1..Dimension(M)] :
        "Argument 2 should be in the range " *
        "[1.." * IntegerToString(Dimension(M)) * "]";
    return M!(M`Module).i;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//             Membership, Parent, and Equality Relations             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic 'in'(x::., M::ModBrdt) -> BoolElt
    {Returns true if x is in X.}
    if Type(x) eq ModBrdtElt then
        if Parent(x) eq M then
            return true;
        elif AmbientModule(Parent(x)) eq AmbientModule(M) then
            return IsCoercible(M`Module,Eltseq(x));
        end if;
    end if;
    return false;
end intrinsic;

intrinsic Parent(x::ModBrdtElt) -> ModBrdt
    {}
    return x`Parent;
end intrinsic;

intrinsic 'eq' (X::ModBrdt,Y::ModBrdt) -> BoolElt
    {}
    if IsIdentical(X,Y) then
        return true;
    elif Degree(X) ne Degree(Y) or 
        Dimension(X) ne Dimension(Y) or 
        not IsIdentical(AmbientModule(X),AmbientModule(Y)) then
        return false;
    end if;
    dim := Dimension(X);
    M := AmbientModule(X)`Module;
    return sub< M | [ BX[i] : i in [1..dim] ] >
        eq sub< M | [ BY[i] : i in [1..dim] ] >
        where BX := BasisMatrix(X) where BY := BasisMatrix(Y); 
end intrinsic;

intrinsic 'eq' (x::ModBrdtElt,y::ModBrdtElt) -> BoolElt
    {}
    return x`Parent eq y`Parent and x`Element eq y`Element;
end intrinsic;

