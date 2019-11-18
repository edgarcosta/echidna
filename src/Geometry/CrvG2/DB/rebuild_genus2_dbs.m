//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//        Copyright (C) 2012 David Kohel <David.Kohel@univ-amu.fr>          //
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
import "extend_genus2_dbs.m": Sprint_counts, 
       IsogenyEquivalenceClass, GaloisOrbitRepresentatives,
       AbsoluteIgusaToIsogenousInvariantsAVI;

//////////////////////////////////////////////////////////////////////////////

intrinsic RebuildGenus2CurvesDatabase(
    Dat::DBUser,chi::RngUPolElt[RngInt],cond::SeqEnum[RngIntElt] :
    Algorithm := "Buggy",
    LocalPrime := 0,
    EndomorphismClass := 0,
    Reverse := false,
    Twist := 1,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    GlobalSubring := false)
    {Given a Frobenius charpoly chi and conductor invariants cond,
    recompute endomorphism rings for these charpoly and conductor,
    rewriting to new endomorphism ring if different.}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of genus 2 curves.";
    if Coefficient(chi,3) gt 0 then chi := Evaluate(chi,-Parent(chi).1); end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool: "Argument 2 is not a valid Frobenius characteristic polynomial.";
    require Type(Twist) eq RngIntElt and Twist in {1,-1} :
        "Parameter \"Twist\" must be +1 or -1.";
    JJ_seqs_seq, ords := IgusaInvariantsSequences(Dat,chi,cond);
    if Algorithm ne "Buggy" then
        Detach(GetEchidnaPackageRoot() * "/Geometry/JacHyp/endomorphism_ring.m");
        Attach(GetEchidnaPackageRoot() * "/Geometry/JacHyp/endomorphism_ring_new.m");
    end if;
    nclass := #JJ_seqs_seq;
    if nclass eq 1 or EndomorphismClass ne 0 then
        vprint Genus2Curves : "Verifying endomorphism rings of 1 endomorphism class.";
    else
        vprintf Genus2Curves : "Verifying endomorphism rings of %o endomorphism classes.\n", nclass;
    end if;
    if EndomorphismClass eq 0 then
        Eclass := [1..nclass];
    else
        require EndomorphismClass ge 1 and EndomorphismClass le nclass :
            "Parameter \"EndomorphismClass\" must be between 1 and " * Sprint(nclass) * ".";
        Eclass := [EndomorphismClass];
    end if;
    PZ<x> := PolynomialRing(IntegerRing());
    FF := FiniteField(p,r);
    case Type(SylowSubgroups):
    when SeqEnum:
        if #SylowSubgroups gt 0 then
            require Type(Universe(SylowSubgroups)) eq RngInt and #SylowSubgroups le 4 :
                "Parameter \"SylowSubgroups\" must be an integer sequence or associative array.";
        end if;
        tors_sub := [ 1 : i in [1..4-#SylowSubgroups] ] cat SylowSubgroups;
        require &and[ tors_sub[i+1] mod tors_sub[i] eq 0 : i in [1..3] ] :
            "Each element of sequence input to parameter \"SylowSubgroups\" must divide successor.";
        primes := #tors_sub eq 0 select [] else PrimeDivisors(tors_sub[#tors_sub]);
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
            "\"SylowSubgroupExtensionFields\" must be a field or associative array.";
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
    for k in Eclass do
        JJ_seqs := JJ_seqs_seq[k];
        if Reverse then
            JJ_seqs := [ JJ_seqs[i] : i in [#JJ_seqs..1 by -1] ];
        end if;
        n := #JJ_seqs div r;
        length_n := #Sprint(n);
        if nclass gt 1 then
            vprintf Genus2Curves : "Verifying endomorphism class %o of %o.\n", k, #JJ_seqs_seq;
        end if;
        vprintf Genus2Curves : "Verifying endomorphism rings of %o conjugacy classes.\n", n;
        for j in [1..n] do
            JJ := JJ_seqs[1+(j-1)*r];
            C := HyperellipticCurveFromIgusaInvariants(JJ);
            if Twist eq 1 then
                if FrobeniusCharacteristicPolynomial(C) ne chi then
                    C := QuadraticTwist(C);
                end if;
            else
                if FrobeniusCharacteristicPolynomial(C) eq chi then
                    C := QuadraticTwist(C);
                end if;
            end if;
            S := ords[k];
            KS := NumberField(S);
            J := Jacobian(C);
	    bad_sylow := false;
            for q in primes do
                if q in Keys(SylowSubgroups) and SylowSubgroups[q] ne [1,1,1,1] then
                    if q in Keys(SylowSubgroupTwists) and SylowSubgroupTwists[q] eq -Twist then
                        Jq := Jacobian(QuadraticTwist(C));
                    else
                        Jq := J;
                    end if;
                    if q in Keys(SylowSubgroupExtensionFields) then
                        Jq := BaseExtend(Jq,SylowSubgroupExtensionFields[q]);
                    end if;
                    invs := AbelianInvariants(SylowSubgroup(Jq,q));
                    invs := [ 1 : i in [1..4-#invs]] cat invs;
                    if &or[ invs[i] mod SylowSubgroups[q][i] ne 0 : i in [1..4] ] then
			bad_sylow := true;
                        if GetVerbose("Genus2Curves_SylowSubgroup") gt 0 then
                            printf "  %o < %o? %o\n", SylowSubgroups[q], invs, false;
                        end if;
			break;
                    end if;
                    printf "  %o < %o? %o\n", SylowSubgroups[q], invs, true;
                end if;
	    end for;
	    if bad_sylow then continue; end if;
            O := MaximalOrder(EndomorphismRingKnownSubring(J));
            KO := NumberField(O);
            assert DefiningPolynomial(KS) eq Evaluate(DefiningPolynomial(KO),Twist*x);
            m := hom< KS->KO | Twist*KO.1 >;
            S := sub< O | [ m(x) : x in Basis(S) ] >;
            LocalRings := AssociativeArray(IntegerRing());
            if LocalPrime ne 0 then
                N := &* FrobeniusVerschiebungConductorAbelianInvariants(chi);
                for l in PrimeDivisors(N) do
                    if l ne LocalPrime then
                        LocalRings[l] := S;
                    end if;
                end for;
            end if;
            if Type(GlobalSubring) eq BoolElt then
                if GlobalSubring then
                    GlobalSubring := S;
                else
                    GlobalSubring := EndomorphismRingKnownSubring(J);
                end if;
            elif Type(GlobalSubring) eq RngOrd then
                KR := NumberField(GlobalSubring);
                require DefiningPolynomial(KR) eq Evaluate(chi,Twist*x) :
                    "Parameter \"GlobalSubring\" must be an order in the number field with defining polynomial ", chi;
                m := hom< KR->KO | KO.1 >;
                GlobalSubring := sub< O | [ m(x) : x in Basis(GlobalSubring) ] >;
            end if;
            O, new_cond := EndomorphismRing(Jacobian(C) :
                LocalRings := LocalRings, GlobalSubring := GlobalSubring);
            if GetVerbose("Genus2Curves") gt 0 then
                strj := Sprint(j);
                while #strj lt length_n do strj := "0" * strj; end while;
                printf "%o %o: %o\n", strj, JJ, new_cond;
            end if;
            if new_cond ne cond then
                Write(Dat,Evaluate(chi,Twist*x),<C,O> : Overwrite);
            end if;
        end for;
    end for;
    if Algorithm ne "Buggy" then
        Detach(GetEchidnaPackageRoot() * "/Geometry/JacHyp/endomorphism_ring_new.m");
        Attach(GetEchidnaPackageRoot() * "/Geometry/JacHyp/endomorphism_ring.m");
    end if;
end intrinsic;

intrinsic RebuildGenus2CurvesDatabaseByIsogeny(
    Dat::DBUser, chi::RngUPolElt[RngInt], cond::SeqEnum[RngIntElt], ell::RngIntElt :
    Algorithm := "",
    BaseExtensionDegree := 1,
    ExtensionDegree := 1,
    ConjugacyClass := 0,
    EndomorphismClass := 0,
    Rosenhain := false,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    IsogenyDepth := 1)
    {Rebuild the database of known invariants with given Frobenius charpoly 
    chi by (ell,ell)-isogenies, overwriting any previously computed invariants.
    The prime ell must not divide [O_K:ZZ[\pi]].}

    /*
    KnownInvariants = set of all known invariants
    Frontier = subset of known invariants which we are expanding
    Frontier_new = new frontier as we expand by breadth-first search
    */
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of genus 2 curves.";
    if Coefficient(chi,3) gt 0 then chi := Evaluate(chi,-Parent(chi).1); end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool : "Argument 2 must be a Frobenius characteristic polynomial.";
    require Type(ExtensionDegree) eq RngIntElt and ExtensionDegree ge 1 :
        "Parameter \"ExtensionDegree\" must be a positive integer.";
    require Type(BaseExtensionDegree) eq RngIntElt and BaseExtensionDegree ge 1 :
        "Parameter \"BaseExtensionDegree\" must be a positive integer.";
    if BaseExtensionDegree gt 1 and ExtensionDegree eq 1 then
        ExtensionDegree := BaseExtensionDegree;
    else
        require ExtensionDegree mod BaseExtensionDegree eq 0 :
            "Parameter \"BaseExtensionDegree\" must divide parameter \"ExtensionDegree\".";
    end if;
    require p ne ell: "Argument 4 must be different from the characteristic.";
    if ExtensionDegree gt BaseExtensionDegree then
        IsogenyDepth := Max(IsogenyDepth,2);
    end if;
    FF := FiniteField(p,BaseExtensionDegree*r);
    KK := FiniteField(p,ExtensionDegree*r);
    q_seq := [ ell ];
    case Type(SylowSubgroups):
    when SeqEnum:
        if #SylowSubgroups gt 0 then
            require Type(Universe(SylowSubgroups)) eq RngInt and #SylowSubgroups le 4 :
                "Parameter \"SylowSubgroups\" must be an integer sequence or associative array.";
        end if;
        tors_sub := [ 1 : i in [1..4-#SylowSubgroups] ] cat SylowSubgroups;
        require &and[ tors_sub[i+1] mod tors_sub[i] eq 0 : i in [1..3] ] :
            "Each element of sequence input to parameter \"SylowSubgroups\" must divide successor.";
        primes := #tors_sub eq 0 select [] else PrimeDivisors(tors_sub[#tors_sub]);
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
    if Rosenhain then
        if IsDefined(SylowSubgroups,2) then
            SylowSubgroups[2] := [ LCM(c,2) : c in SylowSubgroups[2] ];
        else
            SylowSubgroups[2] := [2,2,2,2];
        end if;
    end if;
    primes := [ q : q in q_seq | q notin primes ] cat primes;
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
            "\"SylowSubgroupExtensionFields\" must be a field or associative array.";
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
    JJ_seqs, ords, conds := IgusaInvariantsSequences(Dat,chi);
    ext := BaseExtensionDegree;
    if ext gt 1 then
        R<pi> := quo< Parent(chi) | chi >;
        chi := MinimalPolynomial(pi^ext);
        K<pi1> := NumberField(ords[1]);
        L<pi2> := NumberField(chi); OL := MaximalOrder(L);
        ii := Inverse(hom< L->K | pi1^ext >);
        ords := [ sub< OL | [ ii(c) : c in Basis(O) ] > : O in ords ];
        JJ_seqs := [ [ ChangeUniverse(JJ,KK) : JJ in JJ_seqs[i] ] : i in [1..#JJ_seqs] ];
    end if;
    s := ExtensionDegree;
    frob_cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
    N := #frob_cond eq 0 select 1 else frob_cond[#frob_cond];
    if GetVerbose("Genus2Curves") gt 0 then
        print "Known conductors:";
        DisplayGenus2CurvesNumbers(Dat,chi : Maximal);
    end if;
    Frontier_prev := { Parent([ KK | ]) | };
    j := 0;
    for i in [1..#conds] do
        if cond ne conds[i] then
            continue;
        else
            j +:= 1;
        end if;
        if EndomorphismClass notin {0,j} then
            continue;
        end if;
        KnownInvariants := { IgusaToAbsoluteIgusaInvariants(JJ) : JJ in JJ_seqs[i] };
        if s gt ext then
            KnownInvariants := { ChangeUniverse(jj,KK) : jj in KnownInvariants };
        end if;
        for q in q_seq do
            Extended := false;
            vprintf Genus2Curves : "Extending conductor %o by (%o,%o)-isogenies.\n", conds[i], q, q;
            n := #JJ_seqs[i] div r;
            if ConjugacyClass ne 0 then
                k := ConjugacyClass;
                require Type(Conductor) ne BoolElt :
                    "Parameter \"ConjugacyClass\" can only be specified together with given parameter \"Conductor\".";
                require 1 le k and k le n : "Parameter \"ConjugacyClass\" must be between 1 and " * Sprint(n) * ".";
                Frontier_new := { IgusaToAbsoluteIgusaInvariants(JJ_seqs[i][(k-1)*r+1]) };
            else
                Frontier_new := { IgusaToAbsoluteIgusaInvariants(JJ_seqs[i][(k-1)*r+1]) : k in [1..n] };
            end if;
            if s gt ext then
                Frontier_new := { ChangeUniverse(jj,KK) : jj in Frontier_new };
            end if;
            for depth in [1..IsogenyDepth] do
                Frontier := Frontier_new;
                Frontier_new := { };
                front_num := #Frontier;
                if front_num eq 0 then
                    vprint Genus2Curves : "Terminating extension with empty frontier.";
                    break;
                end if;
                if IsogenyDepth eq 1 then
                    vprintf Genus2Curves : "Extending frontier of %o orbits.\n", front_num;
                else
                    vprintf Genus2Curves : "Depth %2o: Extending frontier of %o orbits.\n", depth, front_num;
                end if;
                count := 0;
                for ii in Frontier do
                    count +:= 1;
                    if Algorithm eq "Avisogenies" or q gt 3 then
                        IsogenousInvariants := AbsoluteIgusaToIsogenousInvariantsAVI(ii,q);
                    else
                        IsogenousInvariants := AbsoluteIgusaToIsogenousInvariants(ii,q);
                    end if;
                    NewInvariants := { jj : jj in IsogenousInvariants | jj notin KnownInvariants };
                    if #NewInvariants gt 0 then
                        strcount := Sprint_counts(count,front_num);
                        vprintf Genus2Curves : "[%o]: Found %o new isogenous invariants ", strcount, #NewInvariants;
                        NewInvariants := GaloisOrbitRepresentatives(NewInvariants,p);
                        vprintf Genus2Curves : "in %o orbits.\n", #NewInvariants;
                        Extended := true;
                    end if;
                    Frontier_new join:= NewInvariants;
                    Frontier_new := GaloisOrbitRepresentatives(Frontier_new,p);
                    for jj in NewInvariants do
                        jj_orbit := { [ ji^(p^k) : ji in jj ] : k in [0..s*r-1] };
                        m := #jj_orbit;
                        if m lt r * ext then
                            printf "Igusa invariants defined over smaller field of degree %o.\n", m;
                            kk := ChangeUniverse(jj,FiniteField(p,m));
                            C := HyperellipticCurveFromAbsoluteIgusaInvariants(kk);
                            xi := FrobeniusCharacteristicPolynomial(C);
                            if Coefficient(chi,3) gt 0 then
                                C := QuadraticTwist(C);
                                xi := FrobeniusCharacteristicPolynomial(C);
                            end if;
                            Write(Dat,xi,C : Overwrite);
                        elif m eq r * ext then
                            kk := ChangeUniverse(jj,FF);
                            C := HyperellipticCurveFromAbsoluteIgusaInvariants(kk);
                            if FrobeniusCharacteristicPolynomial(C) ne chi then
                                C := QuadraticTwist(C);
                            end if;
                            if FrobeniusCharacteristicPolynomial(C) ne chi then
                                for Ci in Twists(C) do
                                    if FrobeniusCharacteristicPolynomial(Ci) eq chi then
                                        C := Ci; break;
                                    end if;
                                end for;
                            end if;
                            if FrobeniusCharacteristicPolynomial(C) ne chi then
                                printf "Igusa invariants do not admit a representative in the isogeny class of %o.\n", chi;
                                continue;
                            end if;
                            J := Jacobian(C);
                            if q in Keys(SylowSubgroups) and SylowSubgroups[q] ne [1,1,1,1] then
                                if q in Keys(SylowSubgroupTwists) and SylowSubgroupTwists[q] eq -1 then
                                    Jq := Jacobian(QuadraticTwist(C));
                                else
                                    Jq := J;
                                end if;
                                if q in Keys(SylowSubgroupExtensionFields) then
                                    Jq := BaseExtend(Jq,SylowSubgroupExtensionFields[q]);
                                end if;
                                invs := AbelianInvariants(SylowSubgroup(Jq,q));
                                invs := [ 1 : i in [1..4-#invs]] cat invs;
                                if &or[ invs[i] mod SylowSubgroups[q][i] ne 0 : i in [1..4] ] then
                                    if GetVerbose("Genus2Curves_SylowSubgroup") gt 0 then
                                        printf "  %o < %o? %o\n", SylowSubgroups[q], invs, false;
                                    end if;
                                    for ji in jj_orbit do Exclude(~Frontier_new,ji); end for;
                                    continue;
                                end if;
                                printf "  %o < %o? %o\n", SylowSubgroups[q], invs, true;
                            end if;
                            O := MaximalOrder(EndomorphismRingKnownSubring(J));
                            S := ords[i];
                            /* The number fields and equation order of O and S should
                            have the same defining polynomials but we need to set up
                            the isomorphism between them. */
                            if DefiningPolynomial(EquationOrder(O)) ne DefiningPolynomial(EquationOrder(S)) then
                                print "O:", DefiningPolynomial(EquationOrder(O));
                                print "S:", DefiningPolynomial(EquationOrder(S));
                                assert false;
                            end if;
                            KO := NumberField(O);
                            KS := NumberField(S);
                            m := hom< KS->KO | KO.1 >;
                            S := sub< O | [ m(x) : x in Basis(ords[i]) ] >;
                            R := sub< O | [ q^depth*x : x in Basis(S) ] >;
                            //
                            LocalRings := AssociativeArray(IntegerRing());
                            for l in PrimeDivisors(N) do
                                if l ne q then
                                    LocalRings[l] := S;
                                end if;
                            end for;
                            O := EndomorphismRing(J :
                                GlobalSubring := R,
                                LocalRings := LocalRings);
                            Write(Dat,chi,<C,O> : Overwrite);
                        end if;
                        KnownInvariants join:= jj_orbit;
                    end for;
                end for;
            end for;
            if GetVerbose("Genus2Curves") gt 0 and Extended then
                print "Currently known conductors:";
                DisplayGenus2CurvesNumbers(Dat,chi : Maximal);
            end if;
        end for;
    end for;
end intrinsic;

