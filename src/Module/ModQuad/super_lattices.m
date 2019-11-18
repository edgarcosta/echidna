////////////////////////////////////////////////////////////////////////
//                                                                    //
//               MAXIMAL INTEGRAL SUPERLATTICE and GENUS              //
//                        David Kohel, 2002                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic MaximalSuperLattice(L::Lat : PreserveEven := false) -> Lat
    {Returns a maximal integral superlattice M of L. 
    If the lattice is even and the parameter PreserveEven 
    is not set to false, then M is also even.}
    require IsIntegral(L) : "Argument must be integral.";
    A := GramMatrix(L);
    prms := PrimeDivisors(Determinant(A));
    for p in prms do
	L := pMaximalSuperLattice(L,p : PreserveEven := PreserveEven);
    end for;
    return  L;
end intrinsic;

intrinsic pMaximalSuperLattice(L::Lat, p::RngIntElt :
    PreserveEven := false) -> Lat
    {Returns a p-maximal integral superlattice M of L. 
    If the lattice is even and the parameter PreserveEven is
    not set to false, then M is also even.}
    require IsIntegral(L) : "Argument must be integral.";
    n := Rank(L);
    FF := FiniteField(p);
    ZZ := Integers();
    has_point := true;
    Even := IsEven(L) and PreserveEven;
    while has_point do
	A := GramMatrix(L);
	K := Kernel(ChangeRing(Parent(A),FF)!A);
	B := [ &+[ ZZ!v[i]*L.i : i in [1..n] ] : v in Basis(K) ];
	if p eq 2 then
	    // Norm(v) = 0 in 2Z/4Z is a linear condition.
	    K := Kernel(Matrix(1,[ FF | ZZ!Norm(v) div 2 : v in B ]));
	    B := [ &+[ ZZ!v[i]*B[i] : i in [1..#B] ] : v in Basis(K) ];
	end if;
	if p eq 2 and Even then
	    D := [ FF | (ZZ!Norm(B[i]) div 4) : i in [1..#B] ];
	    i := Index(D,FF!0);
	else
	    D := [ FF | (ZZ!Norm(B[i]) div p) : i in [1..#B] ];
	    i := Index(D,FF!0);
	end if;
	if i ne 0 then
	    v := B[i];
	elif #B le 1 then
	    has_point := false;
	elif #B eq 2 then
	    if p eq 2 then
		// Even case only reaches here; B[1] and B[2]
		// are not 0 mod 8, so just check B[1]+B[2].
		if ZZ!Norm(B[1]+B[2]) mod 8 eq 0 then
		    v := B[1]+B[2];
		else
		    has_point := false;
		end if;
	    else 
		a := FF!(ZZ!(B[1],B[1]) div p);
		b := FF!(ZZ!(B[2],B[2]) div p);
		t := FF!(ZZ!(B[1],B[2]) div p);
		if a eq 0 then
		    v := B[1];
		elif b eq 0 then
		    v := B[2];
		else
		    has_point, r := IsSquare(t^2-4*a*b);
		    if has_point then
			v := ZZ!(r-t)*B[1] + ZZ!a*B[2];
			assert ZZ!Norm(v) mod p^2 eq 0;
		    end if;
		end if;
	    end if;
	elif #B ge 3 then
	    PP := ProjectiveSpace(FF,2);
	    if p eq 2 then
		f := &+[ D[i]*PP.i^2 : i in [1..3]]
		    + &+[ (ZZ!(B[i],B[j]) div 2)*PP.i*PP.j :
		    i, j in [1..3] | i lt j ];
		X := Scheme(PP,f);
	    else
		f := &+[ D[i]*PP.i^2 : i in [1..3]];
		X := Scheme(PP,f);
	    end if;
	    if IsSingular(X) then
		// scheme always has points...
		P := RationalPoints(X)[1];
	    else
		_, X := IsConic(X); 
		has_point, P := HasPoint(X);
	    end if;
	    if has_point then
		v := &+[ ZZ!P[i]*B[i] : i in [1..3] ];
	    end if;
	end if;
	if has_point then
	    L := sub< (1/p)*L | Basis(L) cat [(1/p)*v] >;
	    vprint Lattice : "Gram matrix L:";
	    vprint Lattice : GramMatrix(L);
	    if Determinant(L) mod p ne 0 then
		has_point := false;
	    end if;
	end if;
    end while;
    return L;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                         MAXIMAL SUPERGENUS                         //
////////////////////////////////////////////////////////////////////////

intrinsic MaximalSuperGenus(G::SymGen : PreserveEven := false) -> SymGen
    {Returns the genus of a maximal integral superlattice of any
    representative lattice.  If the genus is even and the parameter
    PreserveEven is not set to false, then this property is preserved.}
    L := Representative(G);
    M := MaximalSuperLattice(L : PreserveEven := PreserveEven);
    return Genus(CoordinateLattice(M));
end intrinsic;

intrinsic MaximalSuperGenus(G::SymGenLoc :
    PreserveEven := false) -> SymGenLoc
    {Returns the genus of a maximal integral superlattice of any
    representative lattice.  If the genus is even and the parameter
    PreserveEven is not set to false, then this property is preserved.}
    p := Prime(G);
    L := Representative(G);
    M := pMaximalSuperLattice(L,p : PreserveEven := PreserveEven);
    return LocalGenus(CoordinateLattice(M),p);
end intrinsic;
