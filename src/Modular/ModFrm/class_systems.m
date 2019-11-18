////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           CLASS SYSTEMS                            //
//                            David Kohel                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

forward CoprimeForm, TReduction, ModularPowerSeries;

intrinsic ClassSystems(D::RngIntElt,G::GrpPSL2) -> SeqEnum
    {}
    N := Level(G);
    require IsGamma0(G) :
        "Argument 1 must be a gruop of type Gamma_0(N).";
    require D lt 0 and D mod 4 in {0,1} :
        "Argument 2 must be a negative discriminant.";
    Q := QuadraticForms(D);
    _, m := IsSquare(D div FundamentalDiscriminant(D)); 	
    R := [ CoprimeForm(f,N) : f in ReducedForms(Q) ];
    if N eq 1 then return R; end if;
    fac := Factorization(N);
    symbs := [ KroneckerSymbol(D,p[1]) : p in fac ];
    require &and[ symbs[i] eq 1 or
        (symbs[i] eq 0 and fac[i][2] eq 1 and
        m mod fac[i][1] ne 0) : i in [1..#fac] ] :
        "Argument 1 and argument 2 are incompatible.";
    pfrms := [ Q | ];
    for p in fac do
	qq := PrimeForm(Q,p[1]);
	pp := qq;
	for i in [2..p[2]] do
	    qq := Composition(qq,pp);
	end for;
	Append(~pfrms,qq);
    end for;
    Nfrms := [ Q!1 ];
    for i in [1..#pfrms] do
	p1 := pfrms[i];
	if symbs[i] ne 0 then
	    p2 := Conjugate(p1);
	    Nfrms := [ Composition(p1,f) : f in Nfrms ] cat
                     [ Composition(p2,f) : f in Nfrms ];
        else 
	    Nfrms := [ Composition(p1,f) : f in Nfrms ];
	end if;
    end for;
    frmseq := [ [ Composition(nn,f) : f in R ] : nn in Nfrms ];
    return [ [ TReduction(f) : f in frms ] : frms in frmseq ];
end intrinsic;

function TReduction(f)
    a, b := Explode(Eltseq(f));
    return f*Matrix(2,[1,-Sign(b)*((a+Abs(b)-1) div (2*a)),0,1]);
end function;

intrinsic ClassPolynomials(D::RngIntElt,G::GrpPSL2 :
    Precision := 58) -> SeqEnum
    {}
    N := Level(G);
    prec := Precision;
    require IsGamma0(G) :
        "Argument 1 must be a gruop of type Gamma_0(N).";
    require D lt 0 and D mod 4 in {0,1} :
        "Argument 2 must be a negative discriminant.";
    require N in {16,32,64} :
       "Level of argument 2 must be 32 or 64.";
    frms := &cat ClassSystems(D,G);
    f, g := ModularPowerSeries(N,16*prec);
    vprint ClassPolynomial: "Finished power series...";
    // Evaluate the series...
    PZ := PolynomialRing(Integers()); 
    CC := ComplexField(prec); i := CC.1;
    PC := PolynomialRing(CC);
    polys := [ ];
    // for frms in S do
	taus := [ CC | (CC!f[2]+Sqrt(D))/(2*f[1]) : f in frms ];
	qaus := [ Exp(2*Pi(CC)*i*tau) : tau in taus ];
	fseq := [ CC | Evaluate(f,q) : q in qaus ];
	gseq := [ CC | Evaluate(g,q) : q in qaus ];
	prec_new := Max( 
	    Ceiling(1.1*Log(10,1+Abs(Real(&*fseq)))), 
   	    Ceiling(1.1*Log(10,1+Abs(Real(&*gseq)))) );
	if prec lt prec_new then
	    vprint ClassPolynomial : "Setting new precision to ", prec;
	    CC := ComplexField(prec_new);
	    taus := [ CC | (CC!f[2]+Sqrt(D))/(2*f[1]) : f in frms ];
	    ques := [ Exp(2*Pi(CC)*i*tau) : tau in taus ];
	    fseq := [ CC | Evaluate(f,q) : q in ques ];
	    gseq := [ CC | Evaluate(g,q) : q in ques ];
	end if;
	h1 := &*[ X - r : r in fseq ] where X := PC.1;
	h2 := &*[ X - r : r in gseq ] where X := PC.1;
	vprint ClassPolynomial: "h1 =", PolynomialRing(ComplexField(16))!h1;
	vprint ClassPolynomial: "h2 =", PolynomialRing(ComplexField(16))!h2;
	Append(~polys,
	   [ PZ![ Round(Real(c)) : c in Eltseq(h1) ],
	     PZ![ Round(Real(c)) : c in Eltseq(h2) ] ]);
    // end for;
    return polys;
end intrinsic;

function ModularPowerSeries(N,prec)
    PS := LaurentSeriesRing(Rationals());
    k := N in {16,32} select 4 else 2; 
    S := CuspidalSubspace(ModularForms(N,k));
    n := N eq 32 select 8 else 3;
    w := PS!PowerSeries(S.n,prec);
    return PowerSeries(S.(n-1),prec)/w, PowerSeries(S.(n-2),prec)/w;
end function;

function CoprimeForm(f,m)
    a, b, c := Explode(Eltseq(f));
    if GCD(a,m) eq 1 then return f; end if;
    done := false;
    for s in [1..m-1] do
	for r in [1..m-1] do
	    if GCD([r,c]) eq 1 and GCD([a,s]) eq 1 and
		GCD([r,s]) eq 1 then
		n := a*r^2 + b*r*s + c*s^2;
		if GCD(n,m) eq 1 then
		    done := true;
		    r1 := r; s1 := s;
		    t, s2, r2 := XGCD(r1,s1);
		    r2 := -r2;
		    break r;
		end if;
	    end if;
	end for;
	if done then
	    break s;
	end if;
    end for;
    return Parent(f) !
    [ a*r1^2 + b*r1*s1 + c*s1^2,
    2*a*r1*r2 + b*(r1*s2 + r2*s1) + 2*c*s1*s2,
    a*r2^2 + b*r2*s2 + c*s2^2 ];
end function;
