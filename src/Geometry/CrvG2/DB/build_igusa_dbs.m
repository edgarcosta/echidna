//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      IGUSA INVARIANT DATABASES                           //
//         Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu.au>         //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

import "igusa_lix.m": IsValidDAB;
import "genus2_curves.m": IsValidFrobeniusCharpoly;

intrinsic BuildIgusaLIXDatabase(Dat::DBUser,chi::RngUPolElt[RngInt],prec::RngIntElt)
    {Given the database Dat of Igusa LIX invariants and an ordinary
    Frobenius characteristic polynomial, build the corresponding Igusa
    LIX database entry by canonically the associated curves from the
    database.}
    require Degree(chi) eq 4 and IsIrreducible(chi) : "Argument 2 must be irreducible of degree 4.";
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool : "Argument 2 must be a valid Frobenius charpoly.";
    DAB := QuarticCMFieldInvariants(NumberField(chi));
    BuildIgusaLIXDatabase(Dat,DAB,p,prec :
	Conductor := [], FiniteFieldDegree := r, UseCurvesDatabase, GaloisConjugates);
end intrinsic;

intrinsic BuildIgusaLIXDatabase(Dat::DBUser,chi::RngUPolElt[RngInt],cond::[RngIntElt],prec::RngIntElt)
    {Given the database Dat of Igusa LIX invariants and an ordinary
    Frobenius characteristic polynomial, build the corresponding Igusa
    LIX database entry by canonically the associated curves from the
    database.}
    require Degree(chi) eq 4 and IsIrreducible(chi) : "Argument 2 must be irreducible of degree 4.";
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool : "Argument 2 must be a valid Frobenius charpoly.";
    DAB := QuarticCMFieldInvariants(NumberField(chi));
    BuildIgusaLIXDatabase(Dat,DAB,p,prec :
	Conductor := cond, FiniteFieldDegree := r, UseCurvesDatabase, GaloisConjugates);
end intrinsic;

intrinsic BuildIgusaLIXDatabase(
    Dat::DBUser,C::CrvHyp[FldFin],prec::RngIntElt :
    Conductor := [],
    GaloisConjugates := false,
    RelationsDegree := 0)
    {Given the database Dat of Igusa LIX invariants and an ordinary curve
    C with maximal endomorphism ring (or given conductor indices), build
    the corresponding Igusa LIX database entry by canonically lifting C.}
    require Dat`DBIdentifier eq "Igusa LIX" :
        "Argument 1 must be the database of Igusa LIX invariants.";
    // TODO: Allow a parameter to extend database when there is a missing component!
    FF := BaseField(C);
    p := Characteristic(FF);
    g := Genus(C);
    chi := FrobeniusCharacteristicPolynomial(C);
    require g eq 2 and IsIrreducible(chi) and FF!Coefficient(chi,g) ne 0 : 
        "Argument 2 must be an ordinary simple genus 2 curve.";
    DAB := QuarticCMFieldInvariants(NumberField(chi));
    DBCM := QuarticCMFieldDatabase();
    if not DAB in DBCM then Write(DBCM,QuarticCMField(DAB)); end if;
    IgLIX := IgusaLIXInvariants(DAB,p,prec :
        Conductor := Conductor,
        RepresentativeCurve := C,
        GaloisConjugates := GaloisConjugates,
        RelationsDegree := RelationsDegree);
    Write(Dat,<DAB,Conductor>,IgLIX : Overwrite := true);
end intrinsic;

intrinsic BuildIgusaLIXDatabase(
    Dat::DBUser,S::SeqEnum[SeqEnum[FldFinElt]],prec::RngIntElt :
    Conductor := [],
    GaloisConjugates := true,
    RelationsDegree := 0)
    {Given the database Dat of Igusa LIX invariants and an ordinary curve
    C with maximal endomorphism ring (or given conductor indices), build
    the corresponding Igusa LIX database entry by canonically lifting C.}
    require Dat`DBIdentifier eq "Igusa LIX" :
        "Argument 1 must be the database of Igusa LIX invariants.";
    // TODO: Allow a parameter to extend database when there is a missing component!
    JJ := S[1];
    FF := Universe(JJ);
    p := Characteristic(FF); r := Degree(FF);
    C := HyperellipticCurveFromIgusaInvariants(JJ);
    g := Genus(C);
    chi := FrobeniusCharacteristicPolynomial(C);
    if Coefficient(chi,Degree(chi)-1) gt 0 then
        C := QuadraticTwist(C);
        chi := FrobeniusCharacteristicPolynomial(C);
    end if;
    require g eq 2 and IsIrreducible(chi) and FF!Coefficient(chi,g) ne 0 :
        "Argument 2 must be an ordinary simple genus 2 curve.";
    DAB := QuarticCMFieldInvariants(NumberField(chi));
    DBCM := QuarticCMFieldDatabase();
    if not DAB in DBCM then Write(DBCM,QuarticCMField(DAB)); end if;
    S_orbs := { { [ JJ[i]^(p^j) : i in [1..#JJ] ] : j in [0..r-1] } : JJ in S };
    S := [ Representative(orb) : orb in S_orbs ];
    IgLIX := IgusaLIXInvariants(DAB,p,prec :
        Conductor := Conductor,
        RepresentativeCurve := S,
        GaloisConjugates := GaloisConjugates,
        RelationsDegree := RelationsDegree);
    Write(Dat,<DAB,Conductor>,IgLIX : Overwrite := true);
end intrinsic;

intrinsic BuildIgusaLIXDatabase(
    Dat::DBUser,DAB::SeqEnum[RngIntElt],p::RngIntElt,prec::RngIntElt  : 
    Conductor := [],
    RelationsDegree := 0,
    RepresentativeCurve := 0,
    FiniteFieldDegree := 0,
    GaloisConjugates := false,
    UseCurvesDatabase := true)
    {Given the database Dat of Igusa LIX invariants, quartic CM field invariants DAB,
    and a prime p of good ordinary reduction, build the Igusa LIX invariants by
    finding a random ordinary curve of characteristic p with suitable Frobenius
    characteristic polynomial, whose endomorphism ring is maximal.}
    require Dat`DBIdentifier eq "Igusa LIX" :
        "Argument 1 must be the database of Igusa LIX invariants.";
    require #DAB eq 3 :
        "Argument 2 must be a sequence of quartic CM field invariants.";
    D, A, B := Explode(DAB);
    require D mod 4 in {0,1} and D gt 0 and not IsSquare(D) and IsFundamental(D) : 
        "Argument 2 must be a sequence of quartic CM field invariants.";
    require IsSquare((A^2 - 4*B) div D) : 
        "Argument 2 must be a sequence of quartic CM field invariants.";
    // Return if DAB is in database and no representative curve is specified.
    if Type(RepresentativeCurve) eq RngIntElt and <DAB,Conductor> in Dat then
        return;
    end if;
    case Type(RepresentativeCurve):
    when CrvHyp:
        require not GaloisConjugates : "Argument ";
        C := RepresentativeCurve;
        FF := BaseField(C);
        g := Genus(C);
        chi := FrobeniusCharacteristicPolynomial(C);
        require g eq 2 and IsIrreducible(chi) and FF!Coefficient(chi,g) ne 0 : 
            "Argument 2 must be an ordinary simple genus 2 curve.";
        BuildIgusaLIXDatabase(Dat,C,prec : Conductor := Conductor, RelationsDegree := RelationsDegree);
    when RngIntElt:
        PZ := PolynomialRing(IntegerRing()); x := PZ.1;
        K := QuarticCMField(DAB);
        weil_nums := QuarticCMFieldOrdinaryWeilNumbers(K,p);
        require #weil_nums gt 0 :
            "Argument 3 must be a prime of good ordinary reduction.";
        weil_pols := [ PZ | MinimalPolynomial(pi) : pi in weil_nums ];
        vprint IgusaInvariant : "Found Weil polynomials:";
        vprint IgusaInvariant : weil_pols;
        weil_degs := [ Valuation(Evaluate(chi,0),p) div 2 : chi in weil_pols ];
	r := FiniteFieldDegree eq 0 select Min(weil_degs) else FiniteFieldDegree; q := p^r;
	if FiniteFieldDegree eq 0 then
	    weil_pols_mindeg := [ chi : chi in weil_pols | Evaluate(chi,0) eq q^2 ];
	else
	    weil_pols_mindeg := [];
	    for chi in weil_pols do
		q2 := Evaluate(chi,0);
		if q2 eq q^2 then
		    Append(~weil_pols_mindeg,chi);
		elif q2 lt q^2 then
		    k := Round(2*Log(q2,q));
		    if q2^k eq q^2 then
			Append(~weil_pols_mindeg,chi);
		    end if;
		end if;
	    end for;
	end if;
	if #weil_pols_mindeg lt #weil_pols then
	    if FiniteFieldDegree eq 0 then
		vprint IgusaInvariant : "Found minimal degree Weil polynomials:";
	    else
		vprintf IgusaInvariant : "Found degree %o Weil polynomials:\n", r;
	    end if;
	    vprint IgusaInvariant : weil_pols_mindeg;
	end if;
        FF := FiniteField(p,r);
        for chi in weil_pols_mindeg do
            print "Frobenius conductor:", FrobeniusVerschiebungConductorAbelianInvariants(chi);
        end for;
        if UseCurvesDatabase then
            chi := weil_pols_mindeg[1];
            DBG2 := Genus2CurvesDatabase();
	    for JJ_invs in IgusaInvariantsSequences(DBG2,chi,Conductor) do
		BuildIgusaLIXDatabase(Dat,JJ_invs[[1..#JJ_invs by r]],prec :
		    Conductor := Conductor,
		    GaloisConjugates := GaloisConjugates,
		    RelationsDegree := RelationsDegree);
	    end for;
        else
            require not GaloisConjugates :
                "Parameter GaloisConjugates must be false if neither UseCurvesDatabase is true and RepresentativeCurve not specified.";
            JJ_invs := {@ @};
            while true do
                C := RandomOrdinaryGenus2Curve(FF);
                JJ := AbsoluteIgusaInvariants(C);
                if JJ in JJ_invs then continue; end if;
                xi := FrobeniusCharacteristicPolynomial(C);
                yi := Evaluate(xi,-x);
                if xi notin weil_pols_mindeg and yi notin weil_pols_mindeg then
                    continue;
                end if;
                for s in [1..r] do
                    Include(~JJ_invs,[ JJ[i]^p^s : i in [1..#JJ] ]);
                end for;
                print "#JJ_invs:", #JJ_invs;
                J := Jacobian(C);
                R, cond := EndomorphismRing(J);
                print "Endomorphism ring conductor:", cond;
                if Conductor eq cond then break; end if;
            end while;
            BuildIgusaLIXDatabase(Dat,C,prec : Conductor := Conductor, RelationsDegree := RelationsDegree);
        end if;
    else
        require false : "Parameter \"RepresentativeCurve\" must be a curve.";
    end case;
end intrinsic;

intrinsic BuildIgusaLIXDatabase(
    Dat::DBUser,DAB::SeqEnum[RngIntElt],prec::RngIntElt :
    Conductor := [],
    GaloisConjugates := true,
    RelationsDegree := 0,
    RepresentativeIdeal := 0,
    PolarizingElement := 1)
    {Given the database Dat of Igusa LIX invariants, quartic CM field invariants DAB,
    build the Igusa LIX invariants by complex analytic construction with initial precision prec.}
    require Dat`DBIdentifier eq "Igusa LIX" :
        "Argument 1 must be the database of Igusa LIX invariants.";
    require #DAB eq 3 :
        "Argument 2 must be a sequence of quartic CM field invariants.";
    D, A, B := Explode(DAB);
    require D mod 4 in {0,1} and D gt 0 and not IsSquare(D) and IsFundamental(D) : 
        "Argument 2 must be a sequence of quartic CM field invariants.";
    require IsSquare((A^2 - 4*B) div D) : 
        "Argument 2 must be a sequence of quartic CM field invariants.";
    // Return if DAB is in database and no representative ideal is specified.
    if Type(RepresentativeIdeal) eq RngIntElt and <DAB,Conductor> in Dat then
        return;
    end if;
    print "DAB:", DAB;
    IgLIX := IgusaLIXInvariants(DAB,prec :
        Conductor := Conductor,
        GaloisConjugates := GaloisConjugates,
        //RepresentativeIdeal := RepresentativeIdeal,
        PolarizingElement := PolarizingElement,
        RelationsDegree := RelationsDegree);
    IgLIX_seq := IgusaLIXDecomposition(IgLIX);
    print "Found invariants:";
    print IgLIX_seq;
    Write(Dat,DAB,IgLIX_seq : Overwrite := true);
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function IgusaCMHToIgusaLIX(IgCMH)
    QQ := RationalField();
    ZZ := IntegerRing();
    PZ := PolynomialRing(ZZ);
    // Extract data from [ <H1,N1>, <G2,N2>, <G3,N3> ]:
    H1 := IgCMH[1][1]; N1 := IgCMH[1][2]; assert N1 eq ZZ!LeadingCoefficient(H1);
    G2 := IgCMH[2][1]; N2 := IgCMH[2][2];
    G3 := IgCMH[3][1]; N3 := IgCMH[3][2];
    // Extract data from [ <H1,N1>, <G2,N2>, <G3,N3> ]:
    H1_conj := Polynomial([ Trace(c)-c : c in Eltseq(H1) ]);
    if H1_conj ne H1 then 
        H1_abs := PZ!(H1*H1_conj);
        M1 := GCD(Eltseq(H1_abs));
        H1_abs div:= M1;
        N1_lift := LeadingCoefficient(H1_abs);
        if N1_lift lt 0 then N1_lift *:= -1; H1_abs *:= -1; end if;
        N2_lift := M1*N2;
        N3_lift := M1*N3;
        // vprint, IgusaInvariant : "HERE H1";
        // Compute descent of G2 to QQ
        G2_ext := (N1*G2*H1_conj) mod H1;
        G2_ext_conj := Polynomial([ Trace(c)-c : c in Eltseq(G2_ext) ]);
        time G2_lift_seq := [ QQ!c : c in Eltseq(CRT([G2_ext,G2_ext_conj],[H1,H1_conj])) ];
        M2 := LCM([ Denominator(c) : c in G2_lift_seq ]);
        G2_lift_seq := [ ZZ!(M2*c) : c in G2_lift_seq ]; N2_lift *:= M2;
        M2 := GCD([N2_lift] cat G2_lift_seq); 
        G2_lift_seq := [ c div M2 : c in G2_lift_seq ]; N2_lift div:= M2;
        G2_lift := PZ!G2_lift_seq; 
        if N2_lift lt 0 then N2_lift *:= -1; G2_lift *:= -1; end if;
        // vprint, IgusaInvariant : "HERE G2";
        // Compute descent of G3 to QQ
        G3_ext := (N1*G3*H1_conj) mod H1;
        G3_ext_conj := Polynomial([ Trace(c)-c : c in Eltseq(G3_ext) ]);
        time G3_lift_seq := [ QQ!c : c in Eltseq(CRT([G3_ext,G3_ext_conj],[H1,H1_conj])) ];
        M3 := LCM([ Denominator(c) : c in G3_lift_seq ]);
        G3_lift_seq := [ ZZ!(M3*c) : c in G3_lift_seq ]; N3_lift *:= M3;
        M3 := GCD([N3_lift] cat G3_lift_seq); 
        G3_lift_seq := [ c div M3 : c in G3_lift_seq ]; N3_lift div:= M3;
        G3_lift := PZ!G3_lift_seq; 
        if N3_lift lt 0 then N3_lift *:= -1; G3_lift *:= -1; end if;
        // vprint, IgusaInvariant : "HERE G3";
        return [ <H1_abs,1>, <G2_lift,N2_lift>, <G3_lift,N3_lift> ];
    else
        H1 := PZ!IgCMH[1][1]; N1 := IgCMH[1][2]; assert N1 eq ZZ!LeadingCoefficient(H1);
        G2 := PZ!IgCMH[2][1]; N2 := IgCMH[2][2];
        G3 := PZ!IgCMH[3][1]; N3 := IgCMH[3][2];
        // Verify normalization of data [ <H1,N1>, <G2,N2>, <G3,N3> ]:
        if N1 lt 0 then N1 *:= -1; H1 *:= -1; end if;
        if N2 lt 0 then N2 *:= -1; G2 *:= -1; end if;
        if N3 lt 0 then N3 *:= -1; G3 *:= -1; end if;
        assert GCD(Eltseq(H1)) eq 1;
        assert GCD(Eltseq(G2) cat [N2]) eq 1;
        assert GCD(Eltseq(G3) cat [N3]) eq 1;
        return [ <H1,1>, <G2,N2>, <G3,N3> ];
    end if;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic ExtendIgusaLIXDatabaseFromIgusaCMHDatabase(Dat::DBUser,DAB::[RngIntElt] :
    Conductor := [], Overwrite := false, Checkpoints := false, Precision := 0)
    {}
    require Dat`DBIdentifier eq "Igusa LIX" : 
	"Argument 1 must be the database of Igusa LIX invariants.";
    require IsValidDAB(DAB,2) : "Argument 2 must be valid quartic CM invariants.";
    require Conductor eq [] : "Parameter \"Conductor\" must be [].";
    t := QuarticCMFieldType(QuarticCMFieldDatabase(),DAB);
    require t in {[4],[8]} : "Argument 2 must be cyclic or dihedral quartic CM invariants.";
    DBCMH := IgusaCMHDatabase();
    if not <DAB,Conductor,1> in DBCMH then return; end if;
    IgCMHs := IgusaCMHInvariants(DBCMH,DAB : Conductor := Conductor, InvariantType := 1);
    IgLIXs := {@ IgusaCMHToIgusaLIX(IgCMH) : IgCMH in IgCMHs @};
    vprintf IgusaInvariant : "Writing Igusa LIX invariants for %o.\n", DAB;
    Write(Dat,DAB,IgLIXs : Overwrite);
end intrinsic;
