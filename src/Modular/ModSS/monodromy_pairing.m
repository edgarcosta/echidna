////////////////////////////////////////////////////////////////////////
//                       Monodromy Pairing                            //
////////////////////////////////////////////////////////////////////////

/*
Put the inner product structure on the space and just call inner product.
*/

intrinsic MonodromyPairing(x::ModSSElt, y::ModSSElt) -> RngIntElt
    {}
    require AmbientSpace(Parent(x)) eq AmbientSpace(Parent(y)) : 
	"Arguments 1 and 2 must belong to the same space.";
    w := MonodromyWeights(Parent(x));
    xe := Eltseq(x); 
    ye := Eltseq(y);
    return &+[w[i]*xe[i]*ye[i] : i in [1..#w]];
end intrinsic;

function MonodromyWeights_mestre(X)
    // Computes the Eisenstein factor of the Mestre module X.
    assert Type(X) eq ModSS;
    assert UsesMestre(X);
    n := 2;
    N := Level(X);
    while N mod n eq 0 do
	n := NextPrime(n);
    end while;
    T := HeckeOperator(X,n)-(n+1);
    V := Kernel(T);
    while Dimension(V) gt 1 do
	n := NextPrime(n);
	if N mod n ne 0 then
	    T := HeckeOperator(X,n)-(n+1);
	    V := V meet Kernel(T);
	end if;
    end while;
    // Let's just hard code the exceptional automorphims:
    case <Prime(X),AuxiliaryLevel(X)>: 
    when <2,1>:
	w0 := 12;
    when <2,3>:
	w0 := 3;
    when <2,5>:
	w0 := 2;
    when <2,7>:
	w0 := 3;
    when <3,1>:
	w0 := 6;
    when <3,2>:
	w0 := 2;
    when <3,5>:
	w0 := 2;
    else
	w0 := 1;
    end case;
    return [ Integers() | w0*(N div e) : e in eis ]
	where N := LCM(eis) where eis := Eltseq(V.1);
end function;

intrinsic MonodromyWeights(M::ModSS) -> SeqEnum
    {}
    if not IsAmbientSpace(M) then
	return MonodromyWeights(AmbientSpace(M)); 
    end if;
    if not assigned M`monodromy_weights then
	M`monodromy_weights := UsesBrandt(M) select 
	    MonodromyWeights(BrandtModule(M))
	    else MonodromyWeights_mestre(M); 
    end if;
    return M`monodromy_weights;
end intrinsic;

