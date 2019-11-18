////////////////////////////////////////////////////////////////////////
//                                                                    //  
//                        ELLIPTIC MODULAR CURVES                     //
//                             David Kohel                            //
//                           September 2000                           //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

declare verbose ModularCurve, 2;

////////////////////////////////////////////////////////////////////////
//                        Attribute declarations                      //
////////////////////////////////////////////////////////////////////////

declare attributes CrvMod:
   ModelType,          // Classical, Canonical, Atkin, or Default
   Genus,              // Not used, but...
   CuspidalSubscheme,
   AtkinLehnerLevels,
   InvolutionImages,
   EllipticSurfaces,   // Sequence of multivariate polynomials defining
                       // patches of elliptic surfaces over curve
   // For X_0(N):
   ModularInvariants,  // Sequence of elements of psi(x) or P = (x,y)
   QuotientLevels,     // Levels [M,1,1] of quotients to X_0(M)
   QuotientImages,     // Defining polynomials of quotients to X_0(M)
   Eisenstein2, Eisenstein4, Eisenstein6,
   // For X_1(N):
   ModularPoint,       // 
   AffinePolynomial,
   SingularSubscheme,  // Subschemes over which elliptic surface
                       // patches become singular.
   qExpansions,        // q-expansions of generators of function field
   BrandtModule,
   Cusps,              // 
   CuspidalMonoid,
   CharacterImages,
   CharacterGenerators;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                          ATTRIBUTE ACCESS                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic Cusps(X::CrvMod) -> RngIntElt
   {}
   require assigned X`CuspidalSubscheme :
      "Cuspidal subscheme of argument has not been determined.";
   return RationalPoints(CuspidalSubscheme(X));
end intrinsic;

intrinsic CuspidalSubscheme(X::CrvMod) -> RngIntElt
   {}
   require assigned X`CuspidalSubscheme :
      "Cuspidal subscheme of argument has not been determined.";
   return Scheme(X,X`CuspidalSubscheme);
end intrinsic;

/*
This will never be reached, but should set it properly...
intrinsic Genus(X::CrvMod) -> RngIntElt
    {}
    if not assigned X`Genus then
	t := X`ModelIndex; 
	if t eq 0 then
	    X`Genus := ModularGenusX0(Level(X));
	elif t eq 1 then
	    X`Genus := ModularGenusX1(Level(X));
	else 
	    require false : "Not implemented";
	end if;
    end if;
    return X`Genus;
end intrinsic;
*/

CanLvls := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,53,61,67,73,97};
AtkLvls := {2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,71,83,101};

function InvolutionReconstruction(PX,strseq)
    k := 1;
    x := PX.1; j := PX.2; z := PX.3;
    poly := [ PX | ];
    degs := StringToIntegerSequence(strseq[k]);
    for n in degs do
	F := PX!0;
        for i in [0..n] do
	    k +:= 1;
            F +:= StringToInteger(strseq[k])*x^i*z^(n-i);
        end for;;
        Append(~poly, F);
    end for;
    r := Max(degs);
    r1 := Max(degs[1..#degs-1]); r2 := degs[#degs];
    num := &+[ poly[i]*j^(i-1)*z^(r1-degs[i]-i+1) : i in [1..#degs-1] ];
    den := poly[#degs];
    return [ num, den ], r1, r2;
end function;

intrinsic CanonicalInvolution(X::CrvMod) -> Map
    {The canonical involution of the modular curve X.}

    require IsProjective(X) : "Argument 1 must be projective";
    PX := CoordinateRing(X);
    x := PX.1; j := PX.2; z := PX.3;
    model_type := ModelType(X);
    N := Level(X);
    if model_type eq "Classical" then
	if N eq 1 then
	    return iso< X->X | [ -PX.2, -PX.1, PX.3 ], [ -PX.2, -PX.1, PX.3 ] >;
	end if;
	return iso< X->X | [ PX.2, PX.1, PX.3 ], [ PX.2, PX.1, PX.3 ] >;
    elif model_type eq "Atkin" then
	require N in AtkLvls : 
	    "Level of argument, for Atkin models, " *
	    "must be in the set", AtkLvls;
    elif model_type eq "Canonical" then
	require N in CanLvls :
  	    "Level of argument, for canonical models, " * 
	    "must be in the set", CanLvls;
    elif model_type eq "Default" then
	require assigned X`InvolutionImages :
	    "Canonical involution of argument has not been determined.";
	i := Index(X`AtkinLehnerLevels,Level(X));
        return iso< X->X | X`InvolutionImages[i], X`InvolutionImages[i] >;
    else 
	require false : 
	"Model type of argument must be one of \"Atkin\", " *
	"\"Canonical\", \"Classical\", or \"Default\".";
    end if;
    ModEq := GetLibraryRoot() * "/data/ModEq/" * model_type;
    nnn := IntegerToString(N);
    while #nnn lt 3 do nnn := "0" * nnn; end while;
    str := Read(ModEq * "/canonical_involution." * nnn * ".dat");
    jinv, r1, r2 := InvolutionReconstruction(PX,Split(str,"\n"));
    if model_type eq "Atkin" then
	z2 := z^(r1-r2-1);
	return map< X->X | [ x*jinv[2]*z2, jinv[1], z*jinv[2]*z2 ] >;
    else
	s := GCD(N-1,12);
	z2 := z^(r1-r2+1);
	return map< X->X | [ N^s*jinv[2]*z2, x*jinv[1], jinv[2]*z2 ] >;
    end if;
end intrinsic;

intrinsic AtkinLehnerInvolution(X::CrvMod,q::RngIntElt) -> Map
    {The Atkin-Lehner involution of the modular curve X.}

    model_type := ModelType(X);
    if model_type eq "Default" then
	require Level(X) mod q eq 0 and GCD(Level(X) div q,q) eq 1 : 
	   "Argument 2 must be an exact divisor of the level of argument 1.";
	require assigned X`InvolutionImages :
	    "Atkin-Lehner involutions of argument have not been determined.";
	i := Index(X`AtkinLehnerLevels,q);
        return iso< X->X | inv, inv > where inv := X`InvolutionImages[i];
    end if;
    require model_type in {"Atkin", "Canonical", "Classical"} :
	"Model type of argument must be one of \"Atkin\", " *
	"\"Canonical\", \"Classical\", or \"Default\".";
    require q eq Level(X) or model_type eq "Default" : 
       "Argument 2 must equal the level of the curve.";
    require IsProjective(X) : "Argument 1 must be projective";
    return CanonicalInvolution(X);
end intrinsic;

function deltaInvariant(S)
end function;

function Invariant(S)
    a1,a2,a3,a4,a6 := Explode(S);
    b2 := a1^2 + 4*a2;
    b4 := a1*a3 + 2*a4;
    return b2^2 - 24*b4;
end function;

intrinsic BaseCurve(X::CrvMod) -> CrvMod, Map
    {The base curve X(1) of the modular curve X_0(N), followed by
    the projection to this curve.}
    model_type := ModelType(X);
    require model_type in {"Atkin","Canonical","Classical","Default"} : 
        "Model type of argument must be one of \"Atkin\", " *
        "\"Canonical\", \"Classical\" or \"Default\".";
    A := Ambient(X);
    PX := CoordinateRing(A);
    // This is wrong but database reports this...
    // X1 := ModularCurve(A,PX.1+PX.2,"Classical",[1,1,1]);
    // Should be:
    // X1 := ModularCurve(A,PX.1-PX.2,"Classical",[1,1,1]);
    X1 := ModularCurve(A,PX.1-PX.2,"Default",[1,1,1]);
    if ModelType(X) eq "Default" then
	morphs := [];
	ecs := X`EllipticSurfaces;
	for i in [1..#ecs] do
	    wts := [1,2,3,4,6];
	    den := LCM([ c[2] : c in ecs[i] ]);
	    coeffs := [ ecs[i][j][1] *
	        (den^wts[j] div ecs[i][j][2]) : j in [1..5] ];
	    a1,a2,a3,a4,a6 := Explode(coeffs);
	    b2 := a1^2 + 4*a2;
	    b4 := a1*a3 + 2*a4;
	    b6 := a3^2 + 4*a6;
	    b8 := a1^2*a6 - a1*a3*a4 + a2*a3^2 + 4*a2*a6 - a4^2;
	    c4 := b2^2 - 24*b4;
	    delta := -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6;
	    eqns := [ c4^3, c4^3, delta ];
	    Append(~morphs,map< X->X1 | eqns >);
	end for;
	return X1, Explode(morphs);
    end if;
    if IsAffine(A) then
        // return X1, map< X -> X1 | [-PX.2,PX.2] >;
        // Should be:
        return X1, map< X->X1 | [PX.2,PX.2] >;
    else
        // return X1, map< X -> X1 | [-PX.2,PX.2,PX.3] >;
        // Should be:
        return X1, map< X->X1 | [PX.2,PX.2,PX.3] >;
    end if;
end intrinsic;




