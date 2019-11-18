//////////////////////////////////////////////////////////////////////////////
//                                                                          // 
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

declare verbose FldCM, 1;

declare attributes FldNum:
    IsCMField,
    TotallyRealSubfield,
    CMFieldClassInvariants;

intrinsic IsCMField(K::FldNum) -> BoolElt
    {}
    if not assigned K`IsCMField then
	r, s := Signature(K);
	if not r eq 0 then
	    return false;
	elif Degree(K) eq 2 then
	    K`IsCMField := true;
	    K`TotallyRealSubfield := RationalField();
	    return true;
	end if;
	Subflds := [ F[1] : F in Subfields(K) |
	    Degree(F[1]) eq s and IsTotallyReal(F[1]) ];
	if #Subflds ne 1 then
	    return false;
	end if;
	F := Subflds[1];
	K`IsCMField := true;
	K`TotallyRealSubfield := F;
    end if;
    return K`IsCMField;
end intrinsic;

intrinsic ComplexConjugation(K::FldNum) -> Map
    {Given a CM field, returns the complex conjugation map.}
    require IsCMField(K) : "Argument 1 must be a CM field.";
    F := K`TotallyRealSubfield;
    w0 := K!F.1; 
    w1 := K.1;
    auts := Automorphisms(K);
    for s in auts do
	if s(w1) ne w1 and s(w0) eq w0 then return s; end if;
    end for;
end intrinsic;

intrinsic TotallyRealSubfield(K::FldNum) -> FldNum
    {Given a CM field, returns the totally real subfield.}
    require IsCMField(K) : "Argument must be a CM field.";
    if not assigned K`TotallyRealSubfield then
	assert false; // computed by IsCMField
    end if;
    return K`TotallyRealSubfield;    
end intrinsic;

intrinsic TotallyRealSubring(O::RngOrd) -> FldNum
    {Given a CM order, returns the totally real subfield.}
    K := NumberField(O);
    require IsCMField(K) : "Argument must be a CM field.";
    F := TotallyRealSubfield(K);
    X := Basis(O);
    s := ComplexConjugation(K);
    // Construct the smallest symmetric order S containing O:
    Y := [ s(x) : x in X ];
    S := &and [ y in O : y in Y ] select O else Order(X cat Y);
    M := Kernel(Matrix(IntegerRing(),[ Eltseq(S!(x-s(x))) : x in X ]));
    return Order([ F!K!O!Eltseq(x) : x in Basis(M) ]);
end intrinsic;

intrinsic ImaginaryMinkowskiLattice(K::FldNum : Al := "") -> Lat, SeqEnum
    {Given a CM field K, returns the integral Minkowski lattice restricted
    to the purely imaginary sublattice of O_K, followed by a basis for this
    lattice in O_K.}
    require IsCMField(K) : "Argument must be a CM field.";
    return ImaginaryMinkowskiLattice(MaximalOrder(K) : Al := Al);
end intrinsic;

intrinsic ImaginaryMinkowskiLattice(O::RngOrd : Al := "") -> Lat, SeqEnum
    {Given an order O in a CM field, returns the integral Minkowski
    lattice restricted to the purely imaginary sublattice of O,
    followed by a basis for this lattice in O.}
    K := NumberField(O);
    require IsCMField(K) : "Argument must be a CM field.";
    s := ComplexConjugation(K);
    X := Basis(O);
    // Construct the smallest symmetric order S containing O:
    Y := [ s(x) : x in X ];
    S := &and [ y in O : y in Y ] select O else Order(X cat Y);
    N := Kernel(Matrix(IntegerRing(),[ Eltseq(S!(x+s(x))) : x in X ]));
    B := [ O!Eltseq(x) : x in Basis(N) ];
    M := Matrix(IntegerRing(),[ [ -Trace(x*y)/2 : x in B ] : y in B ]);
    if Al eq "" then Al := #B le 4 select "Minkowski" else "LLL"; end if;
    if Al eq "Minkowski" then
	N, U := MinkowskiGramReduction(M : Canonical := #B le 4);
    else
	N, U := LLLGram(M);
    end if;
    deg := Degree(K) div 2;
    C := [ O!Eltseq(&+[ B[j]*U[i,j] : j in [1..deg] ]) : i in [1..deg] ];
    return LatticeWithGram(N), C;
end intrinsic;

intrinsic CMFieldClassNumber(K::FldNum) -> SeqEnum
    {Given a CM field, returns (and caches) the class number.}
    require IsCMField(K) : "Argument must be a CM field.";
    return &*CMFieldClassInvariants(K);
end intrinsic;

intrinsic CMFieldClassInvariants(K::FldNum) -> SeqEnum
    {Given a CM field, returns (and caches) the class group invariants.}
    require IsCMField(K) : "Argument must be a CM field.";
    if not assigned K`CMFieldClassInvariants then
	G := ClassGroup(K);
	K`CMFieldClassInvariants := AbelianInvariants(G);
    end if;
    return K`CMFieldClassInvariants;
end intrinsic;

intrinsic CMFieldInvariants(K::FldNum) -> SeqEnum
    {Given a CM field, returns the CM field invariants.}
    require Degree(K) le 8 and IsCMField(K) : 
	"Argument must be a CM field of degree at most 8.";
    case Degree(K):
    when 2:
	return [ Discriminant(MaximalOrder(K)) ];
    when 4:
	return QuarticCMFieldInvariants(K);
    when 6:
	return SexticCMFieldInvariants(K);
    when 8:
	return OcticCMFieldInvariants(K);
    end case;
end intrinsic;

intrinsic ConductorAbelianInvariants(O::RngOrd) -> SeqEnum
    {}
    OK := MaximalOrder(NumberField(O));
    A := FreeAbelianGroup(Degree(NumberField(O)));
    B := quo< A | [ A!Eltseq(OK!x) : x in Basis(O) ] >;
    return AbelianInvariants(B);
end intrinsic;

intrinsic RealSubringConductorAbelianInvariants(O::RngOrd) -> SeqEnum
    {}
    K := NumberField(O);
    require IsCMField(K) : "Argument must be an order in a CM field.";
    cconj := ComplexConjugation(K);
    F := TotallyRealSubfield(K);
    A := FreeAbelianGroup(Degree(F));
    OF := MaximalOrder(F);
    X := [];
    for x in Basis(O) do
	t := x+cconj(x);
	if t/2 in O then
	    Append(~X,OF!((x+cconj(x))/2));
	else
	    Append(~X,OF!(x+cconj(x)));
	end if;
	Append(~X,x*cconj(x));
    end for;
    R := sub< OF | X >; 
    B := sub< A | [ Eltseq(OF!x) : x in Basis(R) ] >;
    return AbelianInvariants(quo< A | B>);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// Functions related to existence of polarizations of CM lattices.
//////////////////////////////////////////////////////////////////////////////

function QuarticCMElementReduction(pi)
    // Note that if the fundamental unit has norm -1, then we may change 
    // the polarization of the purely imaginary element pi.
    OK := Parent(pi);
    K := NumberField(OK);
    u := FundamentalUnit(TotallyRealSubfield(K));
    s := Trace(-pi^2);
    r := Trace(-(u*pi)^2);
    vprintf FldCM : "r = %o < s = %o?\n", r, s;
    while r lt s do
	vprintf FldCM : "r = %o < s = %o\n", r, s;
	vprint FldCM : "Minpol [incr]:", MinimalPolynomial(pi);
	pi *:= u;
	s := Trace(-pi^2);
	r := Trace(-(u*pi)^2);
    end while;
    u := u^-1;
    s := Trace(-pi^2);
    r := Trace(-(u*pi)^2);
    vprintf FldCM : "r = %o < s = %o?\n", r, s;
    while r lt s do
	vprintf FldCM : "r = %o < s = %o\n", r, s;
	vprint FldCM : "Minpol [decr]:", MinimalPolynomial(pi);
	pi *:= u;
	s := Abs(Log(Abs(Conjugates(-pi^2)[1])));
	r := Abs(Log(Abs(Conjugates(-(u*pi)^2)[1])));
	s := Trace(-pi^2);
	r := Trace(-(u*pi)^2);
    end while;
    vprintf FldCM : "Check: Trace(pi) = %o < Trace(u*pi) = %o: %o\n", t1, t2, t1 lt t2
	where t1 := Trace(-pi^2)/2 where t2 := Trace(-(u*pi)^2)/2;
    vprintf FldCM : "Check: Trace(pi) = %o < Trace(u*pi) = %o: %o\n", t1, t2, t1 lt t2
	where t1 := Trace(-pi^2)/2 where t2 := Trace(-(u^-1*pi)^2)/2;
    vprint FldCM : "Minpol [fine]:", MinimalPolynomial(pi);
    return pi;
end function;

function AdditiveSignatureVector(x)
    return [ FiniteField(2) | (1-Sign(Re(c))) div 2 : c in Conjugates(x) ];
end function;

function TotallyPositiveUnitSubgroup(mF)
    // Given a homomorphism mF: UF -> O_F^* of abelian groups, where F is a totally
    // real field, determine the subgroup UF_plus of UF such that mF(UF_plus) consisting
    // of totally positive units.
    ZZ := IntegerRing();
    UF := Domain(mF);
    r := Ngens(UF);
    M := Matrix([ AdditiveSignatureVector(mF(UF.i)) : i in [1..r] ]);
    N := ChangeRing(BasisMatrix(Kernel(M)),ZZ);
    return sub< UF | [ UF!Eltseq(N[i]) : i in [1..Nrows(N)] ] cat [ 2* UF.i : i in [1..r] ] >;
end function;
	
intrinsic IsPrincipallyPolarizable(O::RngOrd : Reduction := false, ReflexField := false)
    -> BoolElt, RngOrdElt, SeqEnum, SeqEnum
    {Given an ideal I in the maximal O_K order of a CM field K with
    totally real subfield F, returns true, xi, sq_classes, minus_classes
    where I*Ibar*Different(K) = (xi), sq_classes is a sequence of
    representatives for (O_F^*)_+/N(O_K^*), and minus_classes is a
    a sequence of representatives for O_F^*/(O_F^*)_+; otherwise 
    false if no such xi exists}
    require IsCMField(NumberField(O)) : //and IsMaximal(O) : 
	"Argument must be an order in a CM field.";
    unit_ideal := Parent(ideal< O | 1/2 >)!1;
    return IsPrincipallyPolarizable(unit_ideal : Reduction := Reduction, ReflexField := ReflexField);
end intrinsic;

intrinsic IsPrincipallyPolarizable(I::RngOrdIdl : Reduction := false, ReflexField := false)
    -> BoolElt, RngOrdElt, SeqEnum, SeqEnum
    {Given an ideal I in the maximal O_K order of a CM field K with
    totally real subfield F, returns true, xi, sq_classes, minus_classes
    where I*Ibar*Different(K) = (xi), sq_classes is a sequence of
    representatives for (O_F^*)_+/N(O_K^*), and minus_classes is a
    a sequence of representatives for O_F^*/(O_F^*)_+; otherwise 
    false if no such xi exists}
    O := Order(I);
    require IsCMField(NumberField(O)) : "Argument must be an order in a CM field.";
    Frac := Parent(2*ideal< O | 1/2 >);
    return IsPrincipallyPolarizable(Frac!I : Reduction := Reduction, ReflexField := ReflexField);
end intrinsic;

intrinsic IsPrincipallyPolarizable(I::RngOrdFracIdl : Reduction := false, ReflexField := false)
    -> BoolElt, RngOrdElt, SeqEnum, SeqEnum
    {Given a fractional ideal I in the maximal O_K order of a CM field K with
    totally real subfield F, returns true, xi, sq_classes, minus_classes
    where I*Ibar*Different(K) = (xi), sq_classes is a sequence of
    representatives for (O_F^*)_+/N(O_K^*), and minus_classes is a
    a sequence of representatives for O_F^*/<(O_F^*)_+,-1>; otherwise 
    false if no such xi exists.}
    OK := Order(I);
    K := NumberField(OK);
    require IsCMField(K) : //and IsMaximal(OK) : 
	"Argument must be an ideal in an order of a CM field.";
    // We construct the codifferent (= DK^-1) since its inverse DK may not exist.
    coDK := Codifferent(OK);
    c := ComplexConjugation(K);
    J := ideal< OK | [ c(x) : x in Basis(I) ] >;
    X := ColonIdeal(Parent(coDK)!I*J,coDK); // X := I*J*DK;
    bool, pi := IsPrincipal(X);
    if not bool then
        vprint FldCM : "Non-principal ideal.";
        return false, _, _, _;
    end if;
    // Determine if pi is purely imaginary:
    g := Degree(K) div 2;
    UK, mK := UnitGroup(OK);
    F := TotallyRealSubfield(K);
    OF := MaximalOrder(F);
    UF, mF := UnitGroup(OF);
    UF_plus := TotallyPositiveUnitSubgroup(mF);
    UF_mod_UF_plus, proj := quo< UF | UF_plus, [(-1)@@mF] >;
    UF_mod_UF_plus_classes := [ OK!mF(si@@proj) : si in UF_mod_UF_plus  ];
    UF_norm_UK := [ OF!(zi*c(zi)) where zi := mK(UK.(i+1)) : i in [1..g-1] ];
    UF_plus_mod_norm_UK, proj := quo< UF_plus | [ UF_plus!(xi@@mF) : xi in UF_norm_UK ] >;
    UF_plus_mod_norm_UK_classes := [ OK!mF(si@@proj) : si in UF_plus_mod_norm_UK ];
    if c(pi) eq -pi then
	if Reduction then
	    pi := QuarticCMElementReduction(pi);
	end if;
        if Type(ReflexField) ne BoolElt then
            oo := InfinitePlaces(K);
            ww := ReflexField.1;
            ww *:= Sign(Im(Evaluate(K!ww,oo[1])));
            pi *:= Sign(Im(Evaluate(pi,oo[1])));
            for i in [1..#UF_mod_UF_plus_classes] do
                if Sign(Re(Evaluate(UF_mod_UF_plus_classes[i],oo[1]))) lt 0 then
                    UF_mod_UF_plus_classes[i] *:= -1;
                end if;
            end for;
            pi_seq := [ u*pi : u in UF_mod_UF_plus_classes ];
            ww_signs := [ Sign(Im(Evaluate(ww,vi))) : vi in oo ];
            for upi in pi_seq do
                reflex := true;
                for i in [1..#oo] do
                    vi := oo[i];
                    if ww_signs[i] ne Sign(Im(Evaluate(upi,vi))) then
                        reflex := false; break;
                    end if;
                end for;
                if reflex then pi := upi; break; end if;
            end for;
            if not reflex then
                return false, _, _, _;
            end if;
        end if;
        return true, pi, UF_plus_mod_norm_UK_classes, UF_mod_UF_plus_classes;
    end if;
    // Otherwise, consider whether some unit times pi is purely imaginary:
    // We consider representative units in O_K^*/O_K^*^2 up to O_K_tors/<-1>. 
    minus_one := (Order(UK.1) div 2) * UK.1;
    UK_square_quotient, proj := quo< UK | [ minus_one ] cat [ 2 * UK.(i+1) : i in [1..g-1] ] >;
    UK_square_classes := [ mK(si@@proj) : si in UK_square_quotient ];
    for xi in UK_square_classes do
	if c(xi*pi) eq -xi*pi then
	    return true, xi*pi, UF_plus_mod_norm_UK_classes, UF_mod_UF_plus_classes;
	end if;
    end for;
    return false, _, _, _;
end intrinsic;

