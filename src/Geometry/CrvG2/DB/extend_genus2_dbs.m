//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//         Copyright (C) 2009 David Kohel <kohel@iml.univ-mrs.fr>           //
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

//////////////////////////////////////////////////////////////////////////////

function Sprint_counts(k,n)
    sn := Sprint(n);
    kn := "#" * Sprint(k);
    while #kn le #sn do kn := " " * kn; end while;
    return kn * "/" * sn;
end function;

//////////////////////////////////////////////////////////////////////////////

intrinsic ExtendGenus2CurvesDatabaseFromIgusaCMHDatabase(
    Dat::DBUser,chi::RngUPolElt[RngInt] : LiftingPrecision := 0, InvariantType := 2)
    {}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of genus 2 curves.";
    if Coefficient(chi,3) gt 0 then chi := Evaluate(chi,-Parent(chi).1); end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool: "Argument 2 is not a valid Frobenius characteristic polynomial.";
    K := NumberField(chi);
    O := MaximalOrder(K);
    DAB := QuarticCMFieldInvariants(K);
    DBCMH := IgusaCMHDatabase();
    if not <DAB,[],InvariantType> in DBCMH then return; end if;
    FF := FiniteField(p,r);
    for IgCMH in IgusaCMHInvariants(DBCMH,DAB : InvariantType := InvariantType) do
        JJ_seq := IgusaCMHToIgusaInvariants(IgCMH,FF :
            LiftingPrecision := LiftingPrecision, InvariantType := InvariantType);
        JJ_1 := &cat IgusaInvariantsSequences(Dat,chi,[]);
        for JJ in JJ_seq do
            if JJ in JJ_1 then continue; end if;
            C := HyperellipticCurveFromIgusaInvariants(JJ);
            xi := FrobeniusCharacteristicPolynomial(C);
            if Coefficient(xi,3) gt 0 then
                C := QuadraticTwist(C);
                xi := FrobeniusCharacteristicPolynomial(C);
            end if;
            if xi ne chi then
                print "Skipping JJ:", JJ;
                print "...with different Frobenius characteristic polynomial:", xi;
                continue;
            end if;
            Write(Dat,chi,<C,O> : Overwrite);
            JJ_1 := &cat IgusaInvariantsSequences(Dat,chi,[]);
        end for;
    end for;
end intrinsic;

intrinsic ExtendGenus2CurvesDatabaseFromIgusaLIXDatabase(
    Dat::DBUser,chi::RngUPolElt[RngInt] : LiftingPrecision := 0)
    {}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of genus 2 curves.";
    if Coefficient(chi,3) gt 0 then chi := Evaluate(chi,-Parent(chi).1); end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool: "Argument 2 is not a valid Frobenius characteristic polynomial.";
    K := NumberField(chi);
    O := MaximalOrder(K);
    DAB := QuarticCMFieldInvariants(K);
    DBIX := IgusaLIXDatabase();
    if not DAB in DBIX then return; end if;
    FF := FiniteField(p,r);
    for IgLIX in IgusaLIXInvariants(DBIX,DAB) do
        JJ_seq := IgusaLIXToIgusaInvariants(IgLIX,FF : LiftingPrecision := LiftingPrecision);
        JJ_1 := &cat IgusaInvariantsSequences(Dat,chi,[]);
        for JJ in JJ_seq do
            if JJ in JJ_1 then continue; end if;
            C := HyperellipticCurveFromIgusaInvariants(JJ);
            xi := FrobeniusCharacteristicPolynomial(C);
            if Coefficient(xi,3) gt 0 then
                C := QuadraticTwist(C);
                xi := FrobeniusCharacteristicPolynomial(C);
            end if;
            if xi ne chi then
                print "Skipping JJ:", JJ;
                print "...with different Frobenius characteristic polynomial:", xi;
                continue;
            end if;
            Write(Dat,chi,<C,O> : Overwrite);
            JJ_1 := &cat IgusaInvariantsSequences(Dat,chi,[]);
        end for;
    end for;
end intrinsic;

intrinsic ExtendGenus2CurvesDatabaseFromZetaFunctionsDatabase(
    Dat::DBUser,chi::RngUPolElt[RngInt] : DisplayCurvesNumbers := false)
    {}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of genus 2 curves.";
    if Coefficient(chi,3) gt 0 then chi := Evaluate(chi,-Parent(chi).1); end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool: "Argument 2 is not a valid Frobenius characteristic polynomial.";
    DBZ2 := Genus2ZetaFunctionsDatabase();
    if not chi in DBZ2 then return; end if;
    if not chi in Dat then Write(Dat,chi,[]); end if;
    JJ_Z := Genus2ZetaFunctionsIgusaInvariantsSequence(DBZ2,chi);
    vprint Genus2Curves : "Number of invariants in z2 database:", #JJ_Z;
    JJ_S := {@ JJ : JJ in &cat IgusaInvariantsSequences(Dat,chi) @};
    vprint Genus2Curves : "Number of invariants in g2 database:", #JJ_S;
    Extended := false;
    for JJ in JJ_Z[[1..#JJ_Z by r]] do
        if JJ notin JJ_S then
            Write(Dat,chi,JJ : Overwrite);
            Extended := true;
        end if;
    end for;
    if DisplayCurvesNumbers and Extended then
        print "Currently known conductors:";
        DisplayGenus2CurvesNumbers(Dat,chi : Maximal);
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function IsogenyEquivalenceClass(cond,S)
    cond_reduced := cond;
    for ell in S do
        cond_reduced := [ c div ell^Valuation(c,ell) : c in cond_reduced ];
    end for;
    return [ c : c in cond_reduced | c ne 1 ];
end function;

function AbsoluteIgusaToIsogenousInvariantsAVI(jj,ell)
    assert #jj eq 10;
    C := HyperellipticCurveFromAbsoluteIgusaInvariants(jj);
    return [ AbsoluteIgusaInvariants(t[2]) : t in RationallyIsogenousCurvesG2(C,ell) ];
end function;

intrinsic ExtendGenus2CurvesDatabase(
    Dat::DBUser, chi::RngUPolElt[RngInt], cond::SeqEnum[RngIntElt], ell::RngIntElt :
    Algorithm := "",
    BaseExtensionDegree := 1,
    ExtensionDegree := 1,
    ConjugacyClass := 0,
    EndomorphismClass := 0,
    IsogenyDepth := 1,
    IsogenyClass := false,
    Rosenhain := false,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    MaximalIsogenyClass := false)
    {Extend the database of known invariants with given Frobenius charpoly chi by
    (p,p)-isogenies, where p runs through [2,3] or equals the given IsogenyPrime.}
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
    require p eq 2 or p ne ell: "Argument 4 (= " * Sprint(p) * ") must be 2 or different from the characteristic.";
    ExtendGenus2CurvesDatabase(Dat,chi :
        Algorithm := Algorithm,
        Conductor := cond,
        EndomorphismClass := EndomorphismClass,
        IsogenyPrime := ell,
        BaseExtensionDegree := BaseExtensionDegree,
        ExtensionDegree := ExtensionDegree,
        ConjugacyClass := ConjugacyClass,
        IsogenyDepth := IsogenyDepth,
        IsogenyClass := IsogenyClass,
        Rosenhain := Rosenhain,
        SylowSubgroups := SylowSubgroups,
        SylowSubgroupTwists := SylowSubgroupTwists,
        SylowSubgroupExtensionFields := SylowSubgroupExtensionFields,
        MaximalIsogenyClass := MaximalIsogenyClass);
end intrinsic;

intrinsic ExtendGenus2CurvesDatabase(Dat::DBUser,chi::RngUPolElt[RngInt],ell::RngIntElt :
    Algorithm := "",
    Conductor := false,
    EndomorphismClass := 0,
    BaseExtensionDegree := 1,
    ExtensionDegree := 1,
    ConjugacyClass := 0,
    IsogenyDepth := 1,
    IsogenyClass := false,
    Rosenhain := false,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    MaximalIsogenyClass := false)
    {Extend the database of known invariants with given Frobenius charpoly chi by
    (p,p)-isogenies, where p runs through [2,3] or equals the given IsogenyPrime.}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of genus 2 curves.";
    if Coefficient(chi,3) gt 0 then chi := Evaluate(chi,-Parent(chi).1); end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool : "Argument 2 must be a Frobenius characteristic polynomial.";
    require p eq 2 or p ne ell : "Argument 3 must be 2 or different from the characteristic.";
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
    ExtendGenus2CurvesDatabase(Dat,chi :
        Algorithm := Algorithm,
        Conductor := Conductor,
        EndomorphismClass := EndomorphismClass,
        BaseExtensionDegree := BaseExtensionDegree,
        ExtensionDegree := ExtensionDegree,
        ConjugacyClass := ConjugacyClass,
        IsogenyPrime := ell,
        IsogenyDepth := IsogenyDepth,
        IsogenyClass := IsogenyClass,
        Rosenhain := Rosenhain,
        SylowSubgroups := SylowSubgroups,
        SylowSubgroupTwists := SylowSubgroupTwists,
        SylowSubgroupExtensionFields := SylowSubgroupExtensionFields,
        MaximalIsogenyClass := MaximalIsogenyClass);
end intrinsic;

intrinsic ExtendGenus2CurvesDatabase(Dat::DBUser,chi::RngUPolElt[RngInt],cond::SeqEnum[RngIntElt] :
    Algorithm := "",
    BaseExtensionDegree := 1,
    ExtensionDegree := 1,
    ConjugacyClass := 0,
    EndomorphismClass := 0,
    IsogenyPrime := 1,
    IsogenyDepth := 1,
    IsogenyClass := false,
    Rosenhain := false,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    MaximalIsogenyClass := false)
    {Extend the database of known invariants with given Frobenius charpoly chi by
    (p,p)-isogenies, where p runs through [2,3] or equals the given IsogenyPrime.}
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
    require p eq 2 or p ne IsogenyPrime: "\"IsogenyPrime\" must be 2 or different from the characteristic.";
    ExtendGenus2CurvesDatabase(Dat,chi :
        Algorithm := Algorithm,
        Conductor := cond,
        BaseExtensionDegree := BaseExtensionDegree,
        ExtensionDegree := ExtensionDegree,
        ConjugacyClass := ConjugacyClass,
        IsogenyPrime := IsogenyPrime,
        IsogenyDepth := IsogenyDepth,
        IsogenyClass := IsogenyClass,
        Rosenhain := Rosenhain,
        SylowSubgroups := SylowSubgroups,
        SylowSubgroupTwists := SylowSubgroupTwists,
        SylowSubgroupExtensionFields := SylowSubgroupExtensionFields,
        MaximalIsogenyClass := MaximalIsogenyClass);
end intrinsic;

function GaloisOrbitRepresentatives(S,p)
    if #S eq 0 then return S; end if;
    K := Universe(Representative(S));
    s := Valuation(#K,p);
    return { Representative(O) : O in { { [ j^p^i : j in JJ ] : i in [0..s-1] } : JJ in S } };
end function;

intrinsic ExtendGenus2CurvesDatabase(Dat::DBUser,chi::RngUPolElt[RngInt] :
    Algorithm := "",
    Conductor := false,
    EndomorphismClass := 0,
    BaseExtensionDegree := 1,
    ExtensionDegree := 1,
    ConjugacyClass := 0,
    IsogenyPrime := 1,
    IsogenyDepth := 1,
    IsogenyClass := false,
    Rosenhain := false,
    SylowSubgroups := [],
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := false,
    MaximalIsogenyClass := false)
    {Extend the database of known invariants with given Frobenius charpoly chi by
    (p,p)-isogenies, where p runs through [2,3] or equals the given IsogenyPrime.}
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
    require p eq 2 or p ne IsogenyPrime: "\"IsogenyPrime\" must be 2 or different from the characteristic.";
    if ExtensionDegree gt BaseExtensionDegree then
        IsogenyDepth := Max(IsogenyDepth,2);
    end if;
    FF := FiniteField(p,BaseExtensionDegree*r);
    KK := FiniteField(p,ExtensionDegree*r);
    q_seq := IsogenyPrime ne 1 select [ IsogenyPrime ] else p eq 3 select [2] else [2,3];
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
    if s eq 1 then
        KnownInvariants := { IgusaToAbsoluteIgusaInvariants(JJ) : JJ in &cat JJ_seqs };
    else
        KnownInvariants := { IgusaToAbsoluteIgusaInvariants(ChangeUniverse(JJ,KK)) : JJ in &cat JJ_seqs };
    end if;
    cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
    N := #cond eq 0 select 1 else cond[#cond];
    if GetVerbose("Genus2Curves") gt 0 then
        print "Known conductors:";
        DisplayGenus2CurvesNumbers(Dat,chi : Maximal);
    end if;
    Frontier_prev := { Parent([ KK | ]) | };
    case Type(MaximalIsogenyClass):
    when BoolElt:
        max_isogeny_class := MaximalIsogenyClass;
        if max_isogeny_class then
            isogeny_prms := p eq 2 select {@ 2,3 @} else {@ 2 @};
            if IsogenyPrime ne 1 then
                Include(~isogeny_prms,IsogenyPrime);
            end if;
        else
            isogeny_prms := {@ @};
        end if;
    when SeqEnum, SetEnum, SetIndx:
        max_isogeny_class := true;
        isogeny_prms := {@ ell : ell in MaximalIsogenyClass @};
        if IsogenyPrime ne 1 then
            Include(~isogeny_prms,IsogenyPrime);
        end if;
    end case;
    j := 0;
    for i in [1..#conds] do
        if Type(Conductor) eq SeqEnum and Conductor ne conds[i] then
            continue;
        else
            j +:= 1;
            if EndomorphismClass ne 0 and EndomorphismClass ne j then
                continue;
            end if;
        end if;
        for q in q_seq do
            Extended := false;
            if Type(IsogenyClass) eq SeqEnum then
                cond_class := IsogenyEquivalenceClass(IsogenyClass,isogeny_prms);
                if max_isogeny_class and cond_class ne [] then
                    require false : "Parameters IsogenyClass := " * Sprint(IsogenyClass)
                        * "and isogeny prms (= " * Sprint(isogeny_prms) * " not compatible with MaximalIsogenyClass).";
                end if;
                if cond_class ne IsogenyEquivalenceClass(conds[i],isogeny_prms) then
                    continue;
                end if;
            elif max_isogeny_class then
                if IsogenyEquivalenceClass(conds[i],isogeny_prms) ne [] then
                    continue;
                end if;
            end if;
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
                    elif GetVerbose("Genus2Curves") gt 2 then
                        strcount := Sprint_counts(count,front_num);
                        vprintf Genus2Curves : "[%o]: Found 0 new isogenous invariants.\n", strcount;
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


