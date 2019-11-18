////////////////////////////////////////////////////////////////////////
//                                                                    //
//             Generating Relations for Binary Class Groups           //  
//                            David Kohel                             //
//                        Created August 2000                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

declare verbose ClassRelations, 3;

function RandomVector(V,t)
    return V ! [ Random([-t..t]) : j in [1..Degree(V)] ];
end function;

intrinsic SplitPrimes(Q::QuadBin,B::RngIntElt) -> SeqEnum
    {}
    D := Discriminant(Q);
    prime_base := [ Q | ];
    p := 2;
    while p le B do
	if KroneckerSymbol(D,p) eq 1 then
	    Append(~prime_base,PrimeForm(Q,p));
	end if;
	p := NextPrime(p);
    end while;
    return prime_base; 
end intrinsic;

function SmoothReduction(I,gens)
    V := RSpace(Integers(),#gens);
    u := V!0;
    for k in [1..#gens] do 
	p := gens[k][1];
	while I[1] mod p eq 0 do
	    I1 := Composition(I,gens[k] : Reduction := false);
	    if I[1] mod I1[1] eq 0 then 
		I := I1;
		u[k] -:= 1;
	    else 
		I := Composition(I,Conjugate(gens[k]) : Reduction := false);      
		u[k] +:= 1;
	    end if;
	end while;
    end for;
    return I, u;
end function;

intrinsic IsPrimeForm(f::QuadBinElt) -> BoolElt
    {}
    return IsPrime(f[1]);
end intrinsic;

intrinsic IsSmooth(f::QuadBinElt,S::[QuadBinElt] : Check := true) -> BoolElt
    {Returns true if and only if f is expressible in the smooth 
    prime sequence S.}
    if Check then
	require &and[ IsPrimeForm(g) : g in S ] :
	    "Argument 2 must consist of prime forms";
    end if;
    I := SmoothReduction(f,S); 
    return I[1] eq 1;
end intrinsic;

intrinsic ClassRelations(Q::QuadBin,n::RngIntElt : 
    ExtraGenerators := 0) -> ModTupRng {}
    require Category(ExtraGenerators) eq RngIntElt and ExtraGenerators ge 0 : 
	"Parameter 'ExtraGenerators' must be a non-negative integer.";
    D := Discriminant(Q);
    m := Conductor(Q);
    if false then
	h := ClassNumber(Q);
    else
	h := 0;
    end if;
    gens := [ Q | ];
    prm_base := [ Integers() | ];
    p := 2;
    e := ExtraGenerators;
    V0 := RSpace(Integers(),n);
    V1 := RSpace(Integers(),n+e);
    S := [ V1 | ];
    while #gens lt n + e do
	chi := KroneckerSymbol(D,p);
	if chi ne -1 and m mod p ne 0 then 
	    Append(~gens,PrimeForm(Q,p));
	    Append(~prm_base,p);
	    if chi eq 0 then
		// Prime form is a 2-torsion element
		Append(~S,2*V1.#prm_base);
	    end if;
	end if; 
	p := NextPrime(p);
    end while;    
    if GetVerbose("ClassRelations") ge 1 then
	print "Using split primes:", prm_base;  
    end if;
    if h ne 0 then
	S cat:= [ h*V1.i : i in [1..n] ];
    end if;
    r := 0;
    t := 0;
    B0 := Max(2,Ceiling(4*Log(Abs(D))/(n*Log(2))));
    B1 := Max(4,Ceiling(Log(Abs(D))/Log(2)));
    B2 := Max(4,Ceiling(Log(Abs(D))^2));
    if GetVerbose("ClassRelations") ge 2 then
	printf "Using bounds B0 = %o, B1 = %o, B2 = %o\n", B0, B1, B2;
    end if;
    N := 2^Max(n,B1);
    while true do
	t +:= 1;
	if GetVerbose("ClassRelations") ge 1 then
	    print "Iteration:", t;
	end if;
	for k in [1..B2] do
	    v0 := RandomVector(V0,B0);
	    g := &*[ gens[i]^v0[i] : i in [1..n] ];
	    I, u := SmoothReduction(g,gens); 
	    if I[1] eq 1 then
		r1 := Vector([ v0[i] : i in [1..n] ] cat [ 0 : i in [n+1..n+e]]) - 
		    Vector(Eltseq(u)[1..n] cat [ N*u[i] : i in [n+1..n+e] ] );
		if r1 ne 0 then 
		    Append(~S,r1); 
		end if;
	    end if;
	end for;
	vprintf ClassRelations : "#S = %o\n", #S;
	// Matrix needs non-empty sequence
	if #S gt 0 then
	    M := LLL(Matrix(S)); 
	    r := Rank(M);
	    M := Matrix([ M[k] : k in [1..r] ]);
	    S := [ M[i] : i in [1..r] ];
	    vprint ClassRelations, 3 : "Prime base :\n", prm_base;
	    if GetVerbose("ClassRelations") ge 2 then
		print "Relation matrix:"; 
		print M;
	    else
		vprint ClassRelations: "Rank =", r;
	    end if;
	    if r ge n then 
		if &and[ M[i,j] eq 0 : i in [1..n], j in [n+1..n+e] ] then
		    M0 := Matrix(n,n,[ M[i,j] : i, j in [1..n] ]);
		    if h mod Determinant(M0) eq 0 then
			return M0, [ gens[k] : k in [1..n] ];
		    end if;
		end if;      
	    end if;      
	end if;
    end while;
end intrinsic;
