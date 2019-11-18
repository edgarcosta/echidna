//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//  Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>                   //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

import "genus2_curves.m": IsValidFrobeniusCharpoly;

function CMFieldTypeToGaloisGroup(cmfield_type)
    case cmfield_type:
    when [2,2]:
        return "C2 x C2";
    when [4]:
        return "C4";
    when [8]:
        return "D4";
    end case;
end function;

function Frobcharpolycoeffs(C,q : Traces := {})
    s1 := q+1-#C;
    if #Traces ne 0 and s1 notin Traces then return 0, 0, 0; end if;
    if q lt 1024 then
        s2 := (#BaseExtend(C,FiniteField(q^2))-q^2-1+s1^2) div 2;
    else
        n1 := #Jacobian(C); // = (1 + q^2) - s1*(1 + q) + s2;
        s2 := (n1 - (1 + q^2) + s1*(1 + q));
    end if;
    return s1, s2, q;
end function;

intrinsic BuildGenus2CurvesDatabase(Dat::DBUser,chi::RngUPolElt[RngInt],k::RngIntElt :
    RealDiscriminant := 0,
    Level2ThetaNull := false,
    Rosenhain := false,
    ComplementIgusaLIX := true,
    MinimalDefiningField := true,
    DisplayIsogenyClass := false,
    ComputeEndomorphismRing := true,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    MaximalEndomorphismRingSearch := false,
    MaximalCurveFailures := Infinity())
    {}
    require Dat`DBIdentifier eq "Genus 2 curves" : 
        "Argument 1 must be the database of genus 2 curves.";
    bool, p, n := IsPrimePower(Evaluate(chi,0)); r := n div 2;
    BuildGenus2CurvesDatabase(Dat,p,r,k : 
        RealDiscriminant := RealDiscriminant,
        Level2ThetaNull := Level2ThetaNull,
        Rosenhain := Rosenhain,
        Rosenhain := Rosenhain,
        ComplementIgusaLIX := ComplementIgusaLIX,
        MinimalDefiningField := MinimalDefiningField,
        FrobeniusCharacteristicPolynomial := chi,
        DisplayIsogenyClass := DisplayIsogenyClass,
        SylowSubgroups := SylowSubgroups,
        SylowSubgroupTwists := SylowSubgroupTwists,
        SylowSubgroupExtensionFields := SylowSubgroupExtensionFields,
        MaximalEndomorphismRingSearch := MaximalEndomorphismRingSearch,
        MaximalCurveFailures := MaximalCurveFailures);
end intrinsic;

intrinsic BuildGenus2CurvesDatabase(Dat::DBUser,p::RngIntElt,r::RngIntElt,k::RngIntElt :
    ClassNumberBound := 0,
    ExactClassNumber := 0,
    RealDiscriminant := 0,
    SimpleJacobian := true,
    Level2ThetaNull := false,
    Rosenhain := false,
    ComplementIgusaLIX := true,
    MinimalDefiningField := true,
    FrobeniusCharacteristicPolynomial := 0,
    DisplayIsogenyClass := false,
    ComputeEndomorphismRing := true,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    ConductorPrimeBound := 0,
    ConductorInvariants := [ Integers() | ],
    MaximalEndomorphismRingSearch := false,
    MaximalCurveFailures := Infinity())
    {}
    require Dat`DBIdentifier eq "Genus 2 curves" :
        "Argument 1 must be the database of genus 2 curves.";
    if MaximalCurveFailures lt Infinity() then
        max_tot := k + MaximalCurveFailures;
    else
        max_tot := 8*k; // Impose some bound for finite runtime.
    end if;
    h0 := ComputeEndomorphismRing select ExactClassNumber eq 0 select r else ExactClassNumber else 0;
    cond0 := ConductorInvariants;
    DBZ2 := Genus2ZetaFunctionsDatabase();
    DBCM := QuarticCMFieldDatabase();
    DBIX := IgusaLIXDatabase();
    FF := FiniteField(p,r);
    q := p^r;
    if not Level2ThetaNull then
        HumbertDiscs := p eq 2 select {5,8,12,13,17} else {5,8,12,13};
    else
        HumbertDiscs := p eq 2
            select {5,8,9,12,13,17,24,28,40,44,56,60}
            else {4,5,8,9,12,13,16,17,20,24,28,32,40,44,48,52,56,60,68};
    end if;
    case Type(FrobeniusCharacteristicPolynomial):
    when RngIntElt:
        assert FrobeniusCharacteristicPolynomial eq 0;
        xis := {};
    when RngUPolElt:
        xis := {FrobeniusCharacteristicPolynomial};
    when SetEnum:
        xis := FrobeniusCharacteristicPolynomial;
    when SeqEnum:
        xis := SequenceToSet(FrobeniusCharacteristicPolynomial);
    else
        require false: "Parameter \"FrobeniusCharacteristicPolynomial\" must be a polynomial or set or sequence thereof.";
    end case;
    for xi in xis do
        bool, pi, ri := IsValidFrobeniusCharpoly(xi,2);
        require bool and pi eq p and ri eq r :
            "Parameter \"FrobeniusCharacteristicPolynomial\" must specify normalized Frobenius characteristic polynomials of the correct characteristic and degree:", xi;
    end for;
    num := 0;
    tot := 0;
    incr := true;
    case Type(SylowSubgroups):
    when SeqEnum:
	if #SylowSubgroups gt 0 then
	    require Type(Universe(SylowSubgroups)) eq RngInt and #SylowSubgroups le 4 :
		"Parameter \"SylowSubgroups\" must be an integer sequence or associative array.";
	end if;
	tors_sub := [ 1 : i in [1..4-#SylowSubgroups] ] cat SylowSubgroups;
	require &and[ tors_sub[i+1] mod tors_sub[i] eq 0 : i in [1..3] ] :
	    "Each element of sequence input to parameter \"SylowSubgroups\" must divide successor.";
	primes := PrimeDivisors(tors_sub[4]);
	SylowSubgroups := AssociativeArray(IntegerRing());
	for p in primes do
	    SylowSubgroups[p] := [ p^Valuation(c,p) : c in tors_sub ];
	end for;
    when Assoc:
	require Type(Universe(SylowSubgroups)) eq RngInt :
	    "Parameter \"SylowSubgroups\" must be an integer sequence or associative array.";
	primes := Keys(SylowSubgroups);
    else
	require false:
            "Parameter \"SylowSubgroups\" must be an integer sequence or associative array.";
    end case;
    if Type(SylowSubgroupTwists) eq RngIntElt then
        Twsts := AssociativeArray(IntegerRing());
        for q in primes do
            Twsts[q] := SylowSubgroupTwists;
        end for;
        SylowSubgroupTwists := Twsts;
    end if;
    case Type(SylowSubgroupExtensionFields):
    when BoolElt:
        // The default is false (no extension) -- if true raise an error.
        require not SylowSubgroupExtensionFields :
            "Parameter \"SylowSubgroupExtensionFields\" must be a field or associative array.";
        SylowSubgroupExtensionFields := AssociativeArray(IntegerRing());
    when RngIntElt:
        ext_deg := SylowSubgroupExtensionFields;
        KK := FiniteField(p,r*ext_deg); Embed(FF,KK);
        Flds := AssociativeArray(IntegerRing());
        for q in primes do
            Flds[q] := KK;
        end for;
        SylowSubgroupExtensionFields := Flds;
    when FldFin:
        Flds := AssociativeArray(IntegerRing());
        for q in primes do
            Flds[q] := SylowSubgroupExtensionFields;
        end for;
        SylowSubgroupExtensionFields := Flds;
    end case;
    FrobeniusTraces := { IntegerRing() | u*Coefficient(xi,3) : u in [1,-1], xi in xis };
    while num lt k and tot lt max_tot do
        tot +:= 1;
        if incr then
            incr := false;
            printf "num = %o/%o [tot = %o < %o]\n", num, k, tot, max_tot;
        end if;
        if RealDiscriminant eq 0 then
            if Level2ThetaNull then
                C := RandomLevel2ThetaNullGenus2Curve(FF);
            elif Rosenhain then
                C := RandomRosenhainGenus2Curve(FF);
            else
                C := RandomOrdinaryGenus2Curve(FF);
            end if;
        elif RealDiscriminant in HumbertDiscs then
            C := RandomGenus2CurveWithRM(FF,RealDiscriminant :
                Level2ThetaNull := Level2ThetaNull, Rosenhain := Rosenhain);
        else
            require false :
                "Parameter \"RealDiscriminant\" must be in " * Sprint(HumbertDiscs) * ".";
        end if;
        s1, s2 := Frobcharpolycoeffs(C,q : Traces := FrobeniusTraces);
        // Check that the curve has simple Jacobian:
        if s1 eq 0 then continue; end if;
        // Normalize s1:
        if s1 lt 0 then s1 *:= -1; C := QuadraticTwist(C); end if;
        // Check that the curve is ordinary:
        if s2 mod p eq 0 then continue; end if;
        chi := Polynomial([q^2,-q*s1,s2,-s1,1]);
        // Check that given FrobeniusCharacteristicPolynomial(s) include chi:
        if #xis gt 0 and chi notin xis then
            continue;
        end if;
	bad_tors := false;
	for ell in Keys(SylowSubgroups) do
	    if SylowSubgroups[ell] ne [1,1,1,1] then
		if ell in Keys(SylowSubgroupTwists) and SylowSubgroupTwists[ell] eq -1 then
		    J := Jacobian(QuadraticTwist(C));
		else
		    J := Jacobian(C);
		end if;
		if ell in Keys(SylowSubgroupExtensionFields) then
		    J := BaseExtend(J,SylowSubgroupExtensionFields[ell]);
		end if;
		invs := AbelianInvariants(SylowSubgroup(J,ell));
		invs := [ 1 : i in [1..4-#invs] ] cat invs;
		bad_tors := &or[ invs[i] mod SylowSubgroups[ell][i] ne 0 : i in [1..4] ];
		if bad_tors then break; end if;
	    end if;
        end for;
	if bad_tors then print "  Wrong torsion structure:", invs; incr := true; continue; end if;
        JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
        s := LCM([ Degree(MinimalPolynomial(ii)) : ii in JJ ]);
        if s eq r then
            print "  chi:", chi;
        else
            printf "  Igusa invariants defined over smaller field of degree %o.\n", s;
            JJ := ChangeUniverse(JJ,FiniteField(p,s));
            C := HyperellipticCurveFromIgusaInvariants(JJ);
            ps := p^s;
            s1, s2 := Frobcharpolycoeffs(C,ps);
            if s1 lt 0 then s1 *:= -1; C := QuadraticTwist(C); end if;
            chi := Polynomial([ps^2,-ps*s1,s2,-s1,1]);
            printf "  chi: %o (over smaller field)\n", chi;
        end if;
        if IsIrreducible(chi) and not (SimpleJacobian and s1 eq 0) then
            K := NumberField(chi);
            DAB := QuarticCMFieldInvariants(K);
            if DAB in DBCM then
                h := QuarticCMFieldClassNumber(DBCM,DAB);
            else
                h := ClassNumber(K);
            end if;
            if ClassNumberBound ne 0 and ClassNumberBound lt h then
                printf "  Class number: %o (> %o)\n", h, ClassNumberBound;
                incr := true;
                continue;
            end if;
            if not ComplementIgusaLIX and DAB in DBIX then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                print "  DBIX: true (continuing)";
                incr := true;
                continue;
            end if;
            if C in Dat then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                if GetVerbose("Genus2Curves") gt 1 then
                    JJs_seq, _, conds := IgusaInvariantsSequences(Dat,chi);
                    JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
                    i := [ i : i in [1..#JJs_seq] | JJ in JJs_seq[i] ][1];
                    cond := conds[i];
                    printf "  DBG2: true (cond = %o, continuing)\n", cond;
                else
                    print "  DBG2: true (continuing)";
                end if;
                incr := true;
                continue;
            end if;
            if MinimalDefiningField then
                if DAB in DBCM then
                    if h eq 1 then
                        e := 1;
                    else
                        exps := QuarticCMFieldClassInvariants(DBCM,DAB);
                        e := exps[#exps];
                    end if;
                else
                    e := Exponent(ClassGroup(K));
                end if;
                if false then // e mod r ne 0 then
                    /*
                    Counterexample:
                    Over the field F_{2^8} there exists a Frobenius
                    characteristic polynomial:
                       chi: x^4 - 19*x^3 + 457*x^2 - 4864*x + 65536
                    The class group is Z/2Z x Z/20Z, of exponent 20,
                    but the exponent is not divisible by r = 8 and
                    there exists no Frobenius characteristic polynomial
                    of degree 4. 
                    */
                    // If there exists a curve with maximal endomorphism ring
                    // defined over a smaller field then continue:
                    printf "  Class group of exponent %o (!= 0 mod %o) defined over smaller field\n", e, r;
                    incr := true; continue;
                end if;
            end if;
            cmfield_type := QuarticCMFieldType(K);
            if SimpleJacobian and cmfield_type eq [2,2] then
                incr := true; continue;
            end if;
            if DisplayIsogenyClass then
                print "  JJ:", JJ;
            end if;
            print "  Class number:", h;
            print "  CM invariants:", DAB;
            print "  Galois group:", CMFieldTypeToGaloisGroup(cmfield_type);
            print "  chi in DBG2:", chi in Dat;
            print "  chi in DBIX:", DAB in DBIX;
            print "  chi in DBCM:", DAB in DBCM;
            // Write C in the zeta functions database first
            Write(DBZ2,chi,C : Overwrite);
            cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
            print "  Conductor of Z[pi,nu]:", cond;
            if RealDiscriminant ne 0 then
                K<pi> := NumberField(chi);
                OK := MaximalOrder(K);
                F := TotallyRealSubfield(K);
                OF := MaximalOrder(F);
                O := sub< OK | [ pi, p^r/pi ] cat [ K!F!w : w in Basis(OF) ] >;
                cond := ConductorAbelianInvariants(O);
                print "  Conductor of O_F[pi,nu]:", cond;
            end if;
            t := #fac eq 0 select 1 else fac[#fac][1] where fac := Factorization(&*cond);
            if not ComputeEndomorphismRing then
                h := 0;
                cond := [ Integers() | ];
            elif ConductorPrimeBound eq 0 or t le ConductorPrimeBound then
                J := Jacobian(C);
                if RealDiscriminant eq 0 or
                    not IsFundamentalDiscriminant(RealDiscriminant) then
                    R, cond := EndomorphismRing(J);
                else
                    R, cond := EndomorphismRing(J : MaximalRealSubring := true);
                end if;
                cond0 := cond;
            else
                h := 0;
            end if;
        else
            h := 0;
            if SimpleJacobian then
                print "  Skipping split Jacobian."; incr := true; continue;
            end if;
            cond := [ Integers() | ];
        end if;
        if (ExactClassNumber eq 0 or h eq h0) then
            if cond eq cond0 then
                printf "  Accepting cond = %o\n", cond;
                IndentPush();
                Write(Dat,chi,C : Overwrite); // "Overwrite" actually appends...
                if DisplayIsogenyClass then
                    DisplayGenus2CurvesNumbers(Dat,chi);
                end if;
                IndentPop();
                if not DAB in DBCM then
                    Write(DBCM,K);
                end if;
            elif MaximalEndomorphismRingSearch then
                if not IsIrreducible(chi) then
                    print "  Skipping split Jacobian."; incr := true; continue;
                end if;
                K := NumberField(chi); 
                if QuarticCMFieldType(K) eq [2,2] then
                    print "  Skipping split Jacobian."; incr := true; continue;
                end if;
                _, degs := QuarticCMFieldOrdinaryWeilNumbers(K,p);
                if r notin degs then
                    print "  Maximal endomorphism ring not defined over this degree."; incr := true; continue;
                end if;
                IndentPush();
                C := RandomMaximalHyperellipticCurveWithFrobeniusCharpoly(chi);
                IndentPop();
                printf "  Computed curve with maximal conductor\n";
                JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
                s := LCM([ Degree(MinimalPolynomial(ii)) : ii in JJ ]);
                if s ne r then
                    printf "  Invariants defined over subfield of degree %o.\n", s; incr := true; continue;
                end if;
                IndentPush();
                Write(Dat,chi,C : Overwrite);
                if DisplayIsogenyClass then
                    DisplayGenus2CurvesNumbers(Dat,chi);
                end if;
                IndentPop();
                if not DAB in DBCM then
                    Write(DBCM,K);
                end if;
            end if;
            num +:= 1; incr := true;
        else
            printf "  Rejecting cond = %o\n", cond;
        end if;
    end while;
end intrinsic;

intrinsic BuildGenus2CurvesDatabase(Dat::DBUser,p::RngIntElt,r::RngIntElt :
    ClassNumberBound := 0,
    ExactClassNumber := 0,
    RealDiscriminant := 0,
    SimpleJacobian := true,
    IsogenyExtension := false,
    ComplementIgusaLIX := true,
    DisplayIsogenyClass := true,
    MinimalDefiningField := true,
    ComputeEndomorphismRing := true,
    MaximalEndomorphismRingSearch := false,
    FrobeniusCharacteristicPolynomial := 0,
    SylowSubgroups := [],
    ConductorPrimeBound := 0,
    ConductorInvariants := [ Integers() | ])
    {}
    require Dat`DBIdentifier eq "Genus 2 curves" :
        "Argument 1 must be the database of genus 2 curves.";
    require RealDiscriminant eq 0 : "Real discriminant search not implemented.";
    h0 := ComputeEndomorphismRing select ExactClassNumber eq 0 select r else ExactClassNumber else 0;
    cond0 := ConductorInvariants;
    num := 0;
    incr := true;
    DBCM := QuarticCMFieldDatabase();
    DBIX := IgusaLIXDatabase();
    FF := FiniteField(p,r);
    q := p^r;
    case Type(FrobeniusCharacteristicPolynomial):
    when RngIntElt:
        xis := {}; assert FrobeniusCharacteristicPolynomial eq 0;
    when RngUPolElt:
        xis := {FrobeniusCharacteristicPolynomial};
    when SetEnum:
        xis := FrobeniusCharacteristicPolynomial;
    when SeqEnum:
        xis := SequenceToSet(FrobeniusCharacteristicPolynomial);
    else
        require false: "Parameter FrobeniusCharacteristicPolynomial must be a polynomial or set or sequence thereof.";
    end case;
    FrobeniusTraces := { u*Coefficient(xi,3) : u in [1,-1], xi in xis };
    i := Random([1..q]); j := Random([1..q]);
    S3 := [ x : x in FF ];
    S1 := S3[[i..q]] cat S3[[1..i-1]];
    S2 := S3[[j..q]] cat S3[[1..j-1]];
    for x1 in S1, x2 in S2, x3 in S3 do
        ss := [x1,x2,x3];
        if p eq 2 then
            sym1, sym2, sym3 := Explode(ss);
            if sym3 eq 0 then continue; end if;
            j2 := sym2^2/sym3;
            JJ := [ 1, j2, j2^2, sym1^2 + j2^3*(j2 + 1), sym3 ];
        else
            j1, j2, j3 := Explode(ss);
            if j1 eq 0 then continue; end if;
            u1 := 1/j1;
            JJ := [1,j2*u1,j3*u1,(j3-j2^2*u1)*u1/4,u1];
        end if;
        C := HyperellipticCurveFromIgusaInvariants(JJ);
        s1, s2 := Frobcharpolycoeffs(C,q : Traces := FrobeniusTraces);
        // Check that the curve has simple Jacobian:
        if s1 eq 0 then continue; end if;
        // Normalize s1:
        if s1 lt 0 then s1 *:= -1; C := QuadraticTwist(C); end if;
        // Check that the curve is ordinary:
        if s2 mod p eq 0 then continue; end if;
        chi := Polynomial([q^2,-q*s1,s2,-s1,1]);
        // Check that given FrobeniusCharacteristicPolynomial(s) include chi:
        if #xis gt 0 and chi notin xis then
            continue;
        end if;
        JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
        s := LCM([ Degree(MinimalPolynomial(ii)) : ii in JJ ]);
        if s eq r then
            print "  chi:", chi;
        else
            printf "  Igusa invariants defined over smaller field of degree %o.\n", s;
            JJ := ChangeUniverse(JJ,FiniteField(p,s));
            C := HyperellipticCurveFromIgusaInvariants(JJ);
            ps := p^s;
            s1, s2 := Frobcharpolycoeffs(C,ps);
            if s1 lt 0 then s1 *:= -1; C := QuadraticTwist(C); end if;
            chi := Polynomial([ps^2,-ps*s1,s2,-s1,1]);
            printf "  chi: %o (over smaller field)\n", chi;
        end if;
        if IsIrreducible(chi) and not (SimpleJacobian and s1 eq 0) then
            K := NumberField(chi);
            DAB := QuarticCMFieldInvariants(K);
            if DAB in DBCM then
                h := QuarticCMFieldClassNumber(DBCM,DAB);
            else
                h := ClassNumber(K);
            end if;
            if ClassNumberBound ne 0 and ClassNumberBound lt h then
                printf "  Class number: %o (> %o)\n", h, ClassNumberBound; continue;
            end if;
            if not ComplementIgusaLIX and DAB in DBIX then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                print "  DBIX: true (continuing)";
                continue;
            end if;
            if C in Dat then
                print "  Class number:", h;
                print "  CM invariants:", DAB;
                print "  DBG2: true (continuing)";
                incr := true;
                continue;
            end if;
            if MinimalDefiningField then
                if DAB in DBCM then
                    if h eq 1 then
                        e := 1;
                    else
                        exps := QuarticCMFieldClassInvariants(DBCM,DAB);
                        e := exps[#exps];
                    end if;
                else
                    e := Exponent(ClassGroup(K));
                end if;
                if false then
                    /*
                    The following are Frobenius charpolys over the field of 2^8 elements,
                    whose class group has exponent 4 or 12:

                        x^4 - 2*x^3 - 399*x^2 - 512*x + 65536
                        x^4 - 9*x^3 + 161*x^2 - 2304*x + 65536
                        x^4 - 9*x^3 + 289*x^2 - 2304*x + 65536
                        x^4 - 11*x^3 + 465*x^2 - 2816*x + 65536
                        x^4 - 23*x^3 + 345*x^2 - 5888*x + 65536
                        x^4 - 23*x^3 + 513*x^2 - 5888*x + 65536
                        x^4 - 26*x^3 + 345*x^2 - 6656*x + 65536

                    but they do not descend to the field of 2^4 elements.
                    */
                    // If there exists a curve with maximal endomorphism ring
                    // defined over a smaller field then continue:
                    if e mod r ne 0 then
                        printf "  Class group of exponent %o (!= 0 mod %o) defined over smaller field\n", e, r; continue;
                    end if;
                end if;
            end if;
            cmfield_type := QuarticCMFieldType(K);
            if SimpleJacobian and cmfield_type eq [2,2] then
                continue;
            end if;
            if DisplayIsogenyClass then
                print "  JJ:", JJ;
            end if;
            print "  Class number:", h;
            print "  CM invariants:", DAB;
            print "  Galois group:", CMFieldTypeToGaloisGroup(cmfield_type);
            print "  chi in DBG2:", chi in Dat;
            print "  chi in DBIX:", DAB in DBIX;
            print "  chi in DBCM:", DAB in DBCM;
            cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
            print "  Conductor of Z[pi,nu]:", cond;
            if RealDiscriminant ne 0 then
                K<pi> := NumberField(chi);
                OK := MaximalOrder(K);
                F := TotallyRealSubfield(K);
                OF := MaximalOrder(F);
                O := sub< OK | [ pi, p^r/pi ] cat [ K!F!w : w in Basis(OF) ] >;
                cond := ConductorAbelianInvariants(O);
                print "  Conductor of O_F[pi,nu]:", cond;
            end if;
            t := #fac eq 0 select 1 else fac[#fac][1] where fac := Factorization(&*cond);
            if not ComputeEndomorphismRing then
                h := 0;
                cond := [ Integers() | ];
            elif ConductorPrimeBound eq 0 or t le ConductorPrimeBound then
                J := Jacobian(C);
                if RealDiscriminant eq 0 or
                    not IsFundamentalDiscriminant(RealDiscriminant) then
                    R, cond := EndomorphismRing(J);
                else
                    R, cond := EndomorphismRing(J : MaximalRealSubring := true);
                end if;
                cond0 := cond;
            else
                h := 0;
            end if;
        else
            h := 0;
            if SimpleJacobian then
                print "  Skipping split Jacobian."; continue;
            end if;
            cond := [ Integers() | ];
        end if;
        if (ExactClassNumber eq 0 or h eq h0) then
            if cond eq cond0 then
                printf "  Accepting cond = %o\n", cond;
                IndentPush();
                Write(Dat,chi,C : Overwrite); // "Overwrite" actually appends...
                if DisplayIsogenyClass then
                    DisplayGenus2CurvesNumbers(Dat,chi);
                end if;
                if IsogenyExtension then
                    ExtendGenus2CurvesDatabase(Dat,chi);
                end if;
                IndentPop();
                if not DAB in DBCM then
                    Write(DBCM,K);
                end if;
            elif MaximalEndomorphismRingSearch then
                if not IsIrreducible(chi) then
                    print "  Skipping split Jacobian."; continue;
                end if;
                K := NumberField(chi);
                if QuarticCMFieldType(K) eq [2,2] then
                    print "  Skipping split Jacobian."; continue;
                end if;
                _, degs := QuarticCMFieldOrdinaryWeilNumbers(K,p);
                if r notin degs then
                    print "  Maximal endomorphism ring not defined over this degree."; continue;
                end if;
                IndentPush();
                C := RandomMaximalHyperellipticCurveWithFrobeniusCharpoly(chi);
                IndentPop();
                printf "  Computed curve with maximal conductor\n";
                JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
                s := LCM([ Degree(MinimalPolynomial(ii)) : ii in JJ ]);
                if s ne r then
                    printf "  Invariants defined over subfield of degree %o.\n", s; continue;
                end if;
                IndentPush();
                Write(Dat,chi,C : Overwrite);
                if DisplayIsogenyClass then
                    DisplayGenus2CurvesNumbers(Dat,chi);
                end if;
                IndentPop();
                if not DAB in DBCM then
                    Write(DBCM,K);
                end if;
            end if;
        else
            printf "  Rejecting cond = %o\n", cond;
        end if;
    end for;
end intrinsic;

