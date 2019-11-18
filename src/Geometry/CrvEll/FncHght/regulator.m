////////////////////////////////////////////////////////////////////////
//                                                                    //
//       HEIGHT PAIRING AND INDEPENDENCE OF NON-TORSION POINTS        //
//                           David Kohel                              //
//                                                                    //
////////////////////////////////////////////////////////////////////////

Height := Hauteur;
SupportedTypes := {FldRat,FldQuad,FldCyc,FldNum,FldFunRat,FldFun};

intrinsic HeightPairingMatrix(S::[PtEll] : Precision:=20) -> AlgMatElt
    {The height pairing matrix of the sequence S of points on an
    elliptic curve over the rationals.}

    K := Ring(Universe(S));
    if Type(K) notin SupportedTypes then
	require false : 
	"Universe of argument must be defined over a number field " *
	"or function field";
    elif ISA(Type(K),FldAlg) then
	require IsAbsoluteField(K) : 
	    "Universe of argument must be an absolute field.";
    end if;
    RR := ISA(Type(K),FldFun) select Rationals() else RealField();
    M := Zero(MatrixAlgebra(RR,#S));
    for i in [1..#S] do
        M[i,i] := Height(S[i] : Precision := Precision);
        for j in [1..i-1] do
            M[i,j] := (Height(S[i] + S[j] :
                Precision := Precision) - M[i,i] - M[j,j])/2;
            M[j,i] := M[i,j];
        end for;
    end for;
    return M;
end intrinsic;

intrinsic HeightPairingLattice(S::[PtEll] : Precision := 20)
   -> AlgMatElt, Map
   {The height pairing lattice of a sequence of independent points on
   an elliptic curve over Q.}

   E := Curve(Universe(S));
   require Type(Ring(Universe(S))) in {FldNum,FldFun} :
      "Universe of argument 1 must be defined over a global field";
   require IsLinearlyIndependent(S) :
      "Argument is not linearly independent";
   L := LatticeWithGram(HeightPairingMatrix(S : Precision := Precision));
   f := hom< L->E |
       v :-> &+[ E | (Integers()!v[i])*S[i] : i in [1..#S] ] >;
   return L, f;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            REGULATOR                               //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Regulator(S::[PtEll]) -> FldReElt
    {The regulator of the sequence S of points on an elliptic curve
    over a global field, i.e. the determinant of the height pairing
    matrix.}

    require Type(Ring(Universe(S))) in {FldNum,FldFun} :
        "Universe of argument must be defined over a global field";
    return Determinant(HeightPairingMatrix(S : Precision := Precision));
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//               LINEAR DEPENDENCE VIA HEIGHT PAIRING                 //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsLinearlyIndependent(P::PtEll,Q::PtEll :
    Epsilon := 0.1, Precision := 20) -> BoolElt, ModTupRngElt
    {Returns true if and only if P is linearly independent of Q over
    the integers; if false then the second return value is a vector
    giving a linear combination of the points which is torsion (and
    thus in the kernel of the height pairing).}

    PS := Parent(P);
    E := Curve(PS);
    require PS eq Parent(Q) : "Arguments must have the same parent.";
    require Type(Ring(PS)) in SupportedTypes : 
        "Parent of arguments must be defined over a global field.";
    require Type(Epsilon) eq FldReElt and
        0 lt Epsilon and Epsilon lt 1 :
        "Parameter \"Epsilon\" must be a real number between 0 and 1";
    return IsLinearlyIndependent([P,Q]);
end intrinsic;

intrinsic IsLinearlyIndependent(S::[PtEll] :
    Precision := 20, Epsilon := 0.01 ) -> BoolElt, ModTupRngElt
    {Returns true if and only if the sequence of points is linearly
    independent over the integers; if false then the second return
    value is a vector giving a linear combination of the points which
    is torsion (and thus in the kernel of the height pairing).}
        
    PS := Universe(S);
    K := Ring(PS);
    require Type(K) in SupportedTypes : 
        "Universe of argument must be a curve over a global field.";
    require Type(Epsilon) eq FldReElt and
        0 lt Epsilon and Epsilon lt 1 :
        "Parameter \"Epsilon\" must be a real number between 0 and 1";
    if #S eq 0 then return true; end if;

    QQ := RationalField();
    // ToRat:= func< x | x ne 0 select
    // a*2^b where a,b is RealToIntegerExponent(x) else 0 >;
    function ToRat(x)
	if Type(x) eq FldRatElt then
	    return x;
	elif x eq 0 then
	    return 0;
	elif Type(x) eq FldReElt then
	    return a*2^b where a,b is RealToIntegerExponent(x);
	end if;
	assert false;
    end function;
    function ReRound(x)
	if Type(x) eq FldRatElt then
	    return x;
	end if;
	return Round(x);
    end function;
    hi := Height(S[1] : Precision := Precision);
    if hi lt Epsilon then
        v := Vector([1] cat [ 0 : i in [2..#S] ]);
        return false, v;
    end if;
    C := Matrix(1,1,[1]);
    M := Matrix(1,1,[ToRat(hi)]);
    for i in [2..#S] do
        vprint HeightPairing : "Reduced block matrix:";
        vprint HeightPairing : C;
        hi := Height(S[i] : Precision := Precision);
        if hi lt Epsilon then
            v := Vector([ 0 : i in [1..#S] ]);
            v[i] := 1;
            return false, v;
        end if;
        Z := [ 0 : k in [1..i] ];
        C := Matrix(i,&cat[ Eltseq(C[k]) cat [0] : k in [1..i-1] ] cat Z);
        C[i,i] := 1;
        M := Matrix(i,&cat[ Eltseq(M[k]) cat [0] : k in [1..i-1] ] cat Z);
	M[i,i] := ToRat(hi);
        for j in [1..i-1] do
            M[i,j] := (ToRat( Height(S[i] + S[j] :
                Precision := Precision) )- M[i,i] - M[j,j])/2;
            M[j,i] := M[i,j];
        end for;
        if IsPositiveDefinite(M) then
            L := LLL(LatticeWithGram(M));
            B := MatrixAlgebra(Integers(),i)!BasisMatrix(L);
        else
	    if Type(K) eq FldFun then
		RR := RationalField();
	    else
		RR := RealField(16);
	    end if;
            VQ := RSpace(QQ,i);
            D, U := OrthogonalizeGram(M);
            u := [ c/U[i,i] : c in Eltseq(U[i]) ];
            h := M[i,i];
            k := 1;
            while h gt Epsilon do
                v := Vector([ ReRound(RR!(k*u[j])) : j in [1..i] ]);
                h := InnerProduct(VQ!v*M,VQ!v);
                // Q := &+[ v[j]*S[j] : j in [1..i] ];
                // h := Height(Q : Precision := Precision);
                vprint HeightPairing : "Height(Q) =", RR!h;
                vprint HeightPairing : "Vector =", v;
                k +:= 1;
            end while;
            u := Vector(Eltseq(v*C) cat [ 0 : j in [i+1..#S] ]);
            return false, u;
        end if;
        // Apply the reduction to the sequence of points and
        // update the Gram matrix for this reduced basis.
        M := GramMatrix(L);
        S1 := [ &+[ B[k,j]*S[j] : j in [1..i] ] : k in [1..i] ];
        for k in [1..i] do
            S[k] := S1[k];
        end for;
        C := B*C;
        if M[1,1] lt Epsilon then
            v := Vector(Eltseq(C[1]) cat [ 0 : k in [i+1..#S] ]);
            return false, v;
        end if;
    end for;
    return true, _;
end intrinsic;
