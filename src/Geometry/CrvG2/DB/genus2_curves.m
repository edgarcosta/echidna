//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      GENUS 2 CURVES DATABASE                             //
//                                                                          //
//         Copyright (C) 2007 David Kohel <kohel@maths.usyd.edu>            //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

DATDIR := GetEchidnaDatabaseRoot() * "/CrvG2/";
prime_len := 6;
prime_exp := 3;
symm1_len := 6;
symm2_len := 12;

//////////////////////////////////////////////////////////////////////////////

declare verbose Genus2Curves, 4;
declare verbose Genus2Curves_SylowSubgroup, 1;

//////////////////////////////////////////////////////////////////////////////

forward Genus2CurvesDataFile, Genus2CurvesDelete, Genus2CurvesWrite;
forward IsInGenus2CurvesDomain, ExistsGenus2CurvesObject, ExistsGenus2CurvesDataFile;
forward Genus2CurvesSequencesWrite, SortConductorSequences;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function IsValidFrobeniusCharpoly(chi,g)
    if Type(chi) ne RngUPolElt or Degree(chi) ne 2*g then
        return false, _, _, _;
    end if;
    bool, chi := IsCoercible(PolynomialRing(IntegerRing()),chi);
    if not bool then
        return false, _, _, _;
    end if;
    cc := Eltseq(chi);
    if cc[2*g] gt 0 then
        return false, _, _, _;
    end if;
    bool, q := IsPower(cc[1],g);
    if not bool then
        return false, _, _, _;
    end if;
    bool, p, r := IsPrimePower(q);
    if not bool then
        return false, _, _, _;
    end if;
    if &or[ cc[2*g+2-i]*q^(g+1-i) ne cc[i] : i in [1..g+1] ] then
        return false, _, _, _;
    end if;
    return true, p, r, cc;
end function;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic Genus2CurvesDatabase() -> DBUser
    {The database of ordinary genus 2 curves.}
    /*
    Caution: The ExistsFunction is used (and intended) to test whether a
    given object is in the database.  If the input is a Frobenius charpoly
    or quartic CM field invariants, then existence of the data file is
    the desired test.  If the input is a curve or Igusa invariants, then we
    actually need to test whether the representative is stored in the database.
    So ExistsFunction will be defined to be ExistsGenus2CurvesObject, and this
    will wrap the call to ExistsGenus2CurvesDataFile in the former cases and
    membership in that file otherwise.
    */
    Dat := HackobjCreateRaw(DBUser);
    Dat`DBIdentifier := "Genus 2 curves";
    Dat`WriteFunction := Genus2CurvesWrite;
    Dat`DeleteFunction := Genus2CurvesDelete;
    Dat`ExistsFunction := ExistsGenus2CurvesObject;
    Dat`IsInDomainFunction := IsInGenus2CurvesDomain;
    return Dat;
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

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

intrinsic DisplayGenus2CurvesNumbers(Dat::DBUser,chi::RngUPolElt[RngInt] :
    RealConductors := false,
    Gorenstein := false,
    RelativeProjective := false,
    Maximal := false,
    SylowSubgroupPrimes := false,
    SylowSubgroupTwists := 1,
    SylowSubgroupExtensionFields := AssociativeArray(IntegerRing()),
    SylowSubgroupRandomRepresentative := false,
    MaximalIsogenyClass := false,
    OrdinaryPrimes := 0)
    {Display the numbers of invariants for each conductor abelian invariants
    (of the group O_K/O) for each order O containing ZZ[pi,nu] which appears
    in the database.}
    require Dat`DBIdentifier eq "Genus 2 curves" :
        "Argument 1 must be the database of genus 2 curves.";
    if Coefficient(chi,3) gt 0 then
	chi := Evaluate(chi,-Parent(chi).1);
    end if;
    bool, p, r := IsValidFrobeniusCharpoly(chi,2);
    require bool : "Argument 2 must be a valid Frobenius characteristic polynomial.";
    if not chi in Dat then
        Write(Dat,chi,[]);
    end if;
    if Type(SylowSubgroupPrimes) eq BoolElt then
        if SylowSubgroupPrimes then
           cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
           SylowSubgroupPrimes := #cond eq 0 select [] else PrimeDivisors(cond[#cond]);
        else
           SylowSubgroupPrimes := [ IntegerRing() | ];
        end if;
    end if;
    if Type(SylowSubgroupTwists) eq RngIntElt then
	Twsts := AssociativeArray(IntegerRing());
	for q in SylowSubgroupPrimes do
	    Twsts[q] := SylowSubgroupTwists;
	end for;
	SylowSubgroupTwists := Twsts;
    end if;
    require #SylowSubgroupPrimes eq 0 or &and [ IsPrime(ell) : ell in SylowSubgroupPrimes ] :
        "Argument SylowSubgroupPrimes must be a boolean or sequence of primes.";
    case Type(SylowSubgroupExtensionFields):
    when BoolElt:
        // The default is false (no extension) -- if true raise an error.
        require not SylowSubgroupExtensionFields :
            "\"SylowSubgroupExtensionFields\" must be a field or associative array.";
        SylowSubgroupExtensionFields := AssociativeArray(IntegerRing());
    when RngIntElt:
        ext_deg := SylowSubgroupExtensionFields;
	FF := FiniteField(p,r);
	KK := FiniteField(p,r*ext_deg); Embed(FF,KK);
        Flds := AssociativeArray(IntegerRing());
        for q in SylowSubgroupPrimes do
            Flds[q] := KK;
        end for;
        SylowSubgroupExtensionFields := Flds;
    when FldFin:
        Flds := AssociativeArray(IntegerRing());
        for q in SylowSubgroupPrimes do
            Flds[q] := SylowSubgroupExtensionFields;
        end for;
        SylowSubgroupExtensionFields := Flds;
    end case;
    JJ_seqs, ords, conds, rconds := IgusaInvariantsSequences(Dat,chi);
    if Maximal then
        DAB := QuarticCMFieldInvariants(chi);
        print "chi:", chi;
        print "DAB:", DAB;
        if OrdinaryPrimes gt 0 then
            print "Ordinary primes:";
            print QuarticCMFieldOrdinaryPrimes(NumberField(chi),OrdinaryPrimes);
        end if;
	bool_DBIX := chi in IgusaLIXDatabase();
	print "chi in DBIX:", bool_DBIX;
    end if;
    if #JJ_seqs eq 0 then
        cond := FrobeniusVerschiebungConductorAbelianInvariants(chi);
        if Maximal then
            rcond := FrobeniusVerschiebungRealSubringConductorAbelianInvariants(chi);
            printf "%8o: %-16o %o\n", 0, cond, rcond;
        else
            printf "%8o: %o\n", 0, cond;
        end if;
    else
	case Type(MaximalIsogenyClass):
	when BoolElt:
	    max_isogeny_class := MaximalIsogenyClass;
	    if max_isogeny_class then
		isogeny_prms := p eq 2 select {@ 2,3 @} else {@ 2 @};
	    else
		isogeny_prms := {@ @};
	    end if;
	when SeqEnum, SetEnum, SetIndx:
	    max_isogeny_class := true;
	    isogeny_prms := {@ ell : ell in MaximalIsogenyClass @};
	end case;
	for i in [1..#JJ_seqs] do
	    if max_isogeny_class then
		if IsogenyEquivalenceClass(conds[i],isogeny_prms) ne [] then
		    continue;
		end if;
            end if;
	    if Maximal then
                if RealConductors then
                    // let's actually recompute them
                    rcond := RealSubringConductorAbelianInvariants(ords[i]);
                    if Gorenstein then
                        if RelativeProjective then
                            printf "%8o: %-16o %-12o (%5o & %-5o)\n", #JJ_seqs[i],
                                conds[i], rcond, IsGorenstein(ords[i]), IsRelativeProjective(ords[i]);
                        else
                            printf "%8o: %-16o %-12o (%o)\n", #JJ_seqs[i], conds[i], rcond, IsGorenstein(ords[i]);
                        end if;
                    else
                        printf "%8o: %-16o %o\n", #JJ_seqs[i], conds[i], rcond;
                    end if;
                else
                    if Gorenstein then
                        if RelativeProjective then
                            printf "%8o: %-16o %-12o (%5o & %-5o)\n", #JJ_seqs[i],
                                conds[i], rconds[i], IsGorenstein(ords[i]), IsRelativeProjective(ords[i]);
                        else
                            printf "%8o: %-16o %-12o (%o)\n", #JJ_seqs[i], conds[i], rconds[i], IsGorenstein(ords[i]);
                        end if;
                    else
                        printf "%8o: %-16o %o\n", #JJ_seqs[i], conds[i], rconds[i];
                    end if;
                end if;
            else
                printf "%8o: %o\n", #JJ_seqs[i], conds[i];
            end if;
            for q in SylowSubgroupPrimes do
		bool, p, s := IsPrimePower(Evaluate(chi,0)); assert bool; r := s div 2;
		invs_set := {* *};
		num := SylowSubgroupRandomRepresentative select r else #JJ_seqs[i];
		for JJ in JJ_seqs[i][[1..num by r]] do
                    C := HyperellipticCurveFromIgusaInvariants(JJ);
		    twist := FrobeniusCharacteristicPolynomial(C) ne chi;
                    if q in Keys(SylowSubgroupTwists) and SylowSubgroupTwists[q] eq -1 then
			twist := not twist;
                    end if;
		    if twist then
			C := QuadraticTwist(C);
		    end if;
		    Jq := Jacobian(C);
                    if q in Keys(SylowSubgroupExtensionFields) then
                        Jq := BaseExtend(Jq,SylowSubgroupExtensionFields[q]);
                    end if;
                    invs := AbelianInvariants(SylowSubgroup(Jq,q));
                    invs := [ 1 : i in [1..4-#invs]] cat invs;
                    Include(~invs_set,invs);
                end for;
		printf "%4o-Sylow: ", q;
		if SylowSubgroupRandomRepresentative then
		    printf "%o\n", Representative(Set(invs_set));
		else
		    second := false;
		    for invs in Set(invs_set) do
			if second then
			    printf "%12o%o^%o\n", "", invs, Multiplicity(invs_set,invs);
			else
			    printf "%o^%o\n", invs, Multiplicity(invs_set,invs);
			end if;
			second := true;
		    end for;
		end if;
            end for;
        end for;
    end if;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function pad_int(n,r)
    if n lt 0 then
        return "-" * pad_int(-n,r-1);
    end if;
    s := Sprint(Abs(n));
    while #s lt r do
        s := "0" * s;
    end while;
    return s;
end function;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic FrobeniusCharacteristicPolynomials(
    Dat::DBUser,p::RngIntElt,r::RngIntElt) -> SeqEnum
    {The sequence of Frobenius characteristic polynomials for ordinary
    genus 2 curves over the field of p^r elements, represented in the
    database Dat.}
    require Dat`DBIdentifier eq "Genus 2 curves" :
        "Argument 1 must be the database of ordinary curves.";
    prmstg := pad_int(p,prime_len);
    expstg := pad_int(r,prime_exp);
    dirpath := DATDIR * prmstg * "^" * expstg * "/";
    q := p^r;
    P := PolynomialRing(Integers()); x := P.1;
    chi_seq := [ P | ];
    FILES := POpen("find " * dirpath * " -name \"crvg2.*.dbz\"", "r");
    file := Gets(FILES);
    while not IsEof(file) do
        split_string := Split(file,"/");
        chi_str := split_string[#split_string];
        _, s1, s2 := Explode(Split(chi_str,"."));
        s1 := StringToInteger(s1);
        s2 := StringToInteger(s2);
        chi := x^4 - s1*(x^3 + q*x) + s2*x^2 + q^2;
        Append(~chi_seq,chi);
        file := Gets(FILES);
    end while;
    return chi_seq;
end intrinsic;

function Genus2CurvesSequencesMerge(chi, IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq)
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2); assert bool;
    MatQQ := MatrixAlgebra(RationalField(),4);
    MatZZ := MatrixAlgebra(IntegerRing(),4);
    K := NumberField(chi);
    OK := MaximalOrder(K);
    MK := BasisMatrix(OK);
    den := LCM([ Denominator(c) : c in Eltseq(MK) ]);
    MK := MatQQ!EchelonForm(MatZZ!(den*MK))/den;
    BK := [ K!Eltseq(MK[i]) : i in [1..4] ];
    Orders_seq := [ sub< OK | [ &+[ MO[i,j]*BK[j] : j in [1..4] ] : i in [1..4] ] > : MO in OrdersBasis_seq ];
    IgusaInvariants_seqs_new := [];
    OrdersBasis_seq_new := [];
    Conductors_seq_new := [];
    RealConductors_seq_new := [];
    n := #IgusaInvariants_seqs;
    for i in [1..n] do
        cond_test := ConductorAbelianInvariants(Orders_seq[i]) eq Conductors_seq[i];
        if not cond_test then
            // Recompute the endomorphism ring (of the first invariants)
            // before remerge them in the corresponding place.
            JJ := IgusaInvariants_seqs[i][1];
            C := HyperellipticCurveFromIgusaInvariants(JJ);
            if FrobeniusCharacteristicPolynomial(C) ne chi then
                C := QuadraticTwist(C);
            end if;
            J := Jacobian(C);
            O := EndomorphismRing(J);
            baseO := EchelonForm(MatZZ!(BasisMatrix(O)*MK^-1));
            condO := ConductorAbelianInvariants(O);
            condR := RealSubringConductorAbelianInvariants(O);
            OrdersBasis_seq[i] := [ Eltseq(baseO[k]) : k in [1..4] ];
            if condO ne Conductors_seq[i] then
                printf "  Warning: conductors %o -> %o\n", Conductors_seq[i], condO;
                Conductors_seq[i] := condO;
                RealConductors_seq[i] := condR;
            end if;
        end if;
        j := Index(OrdersBasis_seq_new, OrdersBasis_seq[i]);
        if j ne 0 then
            IgusaInvariants_seqs_new[j] cat:= IgusaInvariants_seqs[i];
        else
            Append(~IgusaInvariants_seqs_new,IgusaInvariants_seqs[i]);
            Append(~OrdersBasis_seq_new,OrdersBasis_seq[i]);
            Append(~Conductors_seq_new,Conductors_seq[i]);
            Append(~RealConductors_seq_new,RealConductors_seq[i]);
        end if;
    end for;
    return IgusaInvariants_seqs_new, OrdersBasis_seq_new, Conductors_seq_new, RealConductors_seq_new;
end function;


function Genus2CurvesSequencesRead(chi)
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2); assert bool;
    bool, filename := ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3]; assert bool;
    FF := FiniteField(p,r);
    PF := PolynomialRing(FF);
    // TODO: What happens when chi is reducible???
    K := NumberField(chi);
    OK := MaximalOrder(K);
    O_FrobVer := sub< OK | K.1, p^r/K.1 >;
    IgusaInvariants_seqs := [ ];
    OrdersBasis_seq := [ ];
    Conductors_seq := [ ];
    RealConductors_seq := [ ];
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    // 1. [1] the quartic CM field invariants D, A, B;
    DAB_string := Gets(file);
    if IsEof(DAB_string) then
        error if true, "Corrupt file: " * filename;
    end if;
    DAB := StringToIntegerSequence(DAB_string);
    // 2. [1] the type of quartic CM field:
    t := StringToInteger(Gets(file));
    // 3. [1] the class group abelian invariants of O_K [ h1_i ];
    h1_invs := StringToIntegerSequence(Gets(file));
    // 4. [1] the narrow class group abelian invariants of O_F [ h2_i ];
    h2_invs := StringToIntegerSequence(Gets(file));
    // 5. [1] the abelian group invariants of O_K/\ZZ[\pi,\bar\pi];
    condK := StringToIntegerSequence(Gets(file));
    while 1 in condK do Remove(~condK,1); end while;
    // 6. [1] the abelian group invariants of O_F/O_F \cap \ZZ[\pi,\bar\pi];
    condF := StringToIntegerSequence(Gets(file));
    while 1 in condF do Remove(~condF,1); end while;
    // 7. [4] the basis matrix for O_K in terms of the power basis for \QQ(\pi).
    MK := [];
    for i in [1..4] do
        v := StringToIntegerSequence(Gets(file));
        Append(~MK,[ v[j]/v[5] : j in [1..4] ]);
    end for;
    BK := [ K!MK[i] : i in [1..4] ];
    // 8. the coefficients of the minimal polynomial of \FF_{p^r}.
    cffs := StringToIntegerSequence(Gets(file));
    if Eltseq(DefiningPolynomial(FF)) ne cffs then
        print "DAB:", DAB;
        print "Frobenius charpoly:", chi;
        print "Defining polynomial coeffs:", Eltseq(DefiningPolynomial(FF));
        print "Nondefault database coeffs:", cffs;
        error if true, "Database has non-default defining polynomial for finite field.";
    end if;
    while true do
        condO_string := Gets(file);
        if IsEof(condO_string) then break; end if;
        // 9. for each endomorphism ring O in \ZZ[\pi,\bar\pi] \subseteq O \subseteq O_K:
        //   a. [1] the abelian group invariants of O_K/O;
        condO := StringToIntegerSequence(condO_string);
        while 1 in condO do Remove(~condO,1); end while;
        if condO eq [0] then
            O := O_FrobVer;
        else
            //   b. [1] the abelian group invariants of O_F/(O \cup O_F);
            condR := StringToIntegerSequence(Gets(file));
            while 1 in condR do Remove(~condR,1); end while;
            //   c. [4] the integral basis matrix of O in O_K;
            MO := [];
            for i in [1..4] do
                Append(~MO,StringToIntegerSequence(Gets(file)));
            end for;
        end if;
        //   d. [1] the number of invariants known = n
        num := StringToInteger(Gets(file));
        //  e. [1] times num:
        //         the concatenated sequence of five normalized Igusa invariants
        JJ_seq := [ ];
        for i in [1..num] do
            JJ_cat := StringToIntegerSequence(Gets(file));
            Append(~JJ_seq,[ FF!JJ_cat[[r*j+1..r*(j+1)]] : j in [0..4] ]);
        end for;
        Append(~IgusaInvariants_seqs,JJ_seq);
        Append(~OrdersBasis_seq,MO);
        Append(~Conductors_seq,condO);
        Append(~RealConductors_seq,condR);
    end while;
    delete file;
    if #OrdersBasis_seq ne #SequenceToSet(OrdersBasis_seq) then
        print "  Merging invariants with the same orders.";
        IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq :=
            Genus2CurvesSequencesMerge(chi, IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq);
        assert #OrdersBasis_seq eq #SequenceToSet(OrdersBasis_seq);
        Genus2CurvesSequencesWrite(chi, IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq);
        return Genus2CurvesSequencesRead(chi);
    end if;
    return IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq, DAB, h1_invs, h2_invs;
end function;

intrinsic IgusaInvariantsSequences(Dat::DBUser,chi::RngUPolElt,cond::SeqEnum[RngIntElt])
    -> SeqEnum, SeqEnum, SeqEnum, SeqEnum
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, returns the sequence of normalized Igusa invariants
    of curves with this characteristic polynomial.}

    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of ordinary curves.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    bool, filename := ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    require bool : "Argument 1 contains no data file for this Frobenius characteristic polynomial.";
    IgusaInvariants_seqs, OrdersBasis_seq,
        Conductors_seq, RealConductors_seq, DAB, h1_invs,  h2_invs := Genus2CurvesSequencesRead(chi);
    // Ignoring the stored Echelonized basis matrix for OK.
    MatQQ := MatrixAlgebra(RationalField(),4);
    MatZZ := MatrixAlgebra(IntegerRing(),4);
    n := #Conductors_seq;
    I := [ i : i in [1..n] | Conductors_seq[i] eq cond ];
    K := NumberField(chi);
    OK := MaximalOrder(K);
    MK := BasisMatrix(OK);
    den := LCM([ Denominator(c) : c in Eltseq(MK) ]);
    MK := MatQQ!EchelonForm(MatZZ!(den*MK))/den;
    BK := [ K!Eltseq(MK[i]) : i in [1..4] ];
    Orders_seq := [ sub< OK | [ &+[ MO[i,j]*BK[j] : j in [1..4] ] : i in [1..4] ] > : MO in OrdersBasis_seq[I] ];
    return IgusaInvariants_seqs[I], Orders_seq, DAB, h1_invs, h2_invs;
end intrinsic;

intrinsic IgusaInvariantsSequences(Dat::DBUser,chi::RngUPolElt)
    -> SeqEnum, SeqEnum, SeqEnum, SeqEnum, SeqEnum
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, returns the sequence of normalized Igusa invariants
    of curves with this characteristic polynomial.}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of ordinary curves.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    bool, filename := ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    require bool : "Argument 1 contains no data file for this Frobenius characteristic polynomial.";
    IgusaInvariants_seqs, OrdersBasis_seq,
        Conductors_seq, RealConductors_seq, DAB, h1_invs,  h2_invs := Genus2CurvesSequencesRead(chi);
    MatQQ := MatrixAlgebra(RationalField(),4);
    MatZZ := MatrixAlgebra(IntegerRing(),4);
    K := NumberField(chi);
    OK := MaximalOrder(K);
    MK := BasisMatrix(OK);
    den := LCM([ Denominator(c) : c in Eltseq(MK) ]);
    MK := MatQQ!EchelonForm(MatZZ!(den*MK))/den;
    BK := [ K!Eltseq(MK[i]) : i in [1..4] ];
    Orders_seq := [ sub< OK | [ &+[ MO[i,j]*BK[j] : j in [1..4] ] : i in [1..4] ] > : MO in OrdersBasis_seq ];
    return IgusaInvariants_seqs, Orders_seq, Conductors_seq, RealConductors_seq, DAB, h1_invs, h2_invs;
end intrinsic;

intrinsic QuarticCMFieldInvariants(Dat::DBUser,chi::RngUPolElt) -> SeqEnum
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, returns the sequence of quartic CM field invariants.}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of ordinary curves.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    require IsIrreducible(chi) : "Argument 2 must be irreducible.";
    bool, filename := ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    require bool : "Argument 1 contains no data file for this Frobenius characteristic polynomial.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    DAB_string := Gets(file);
    if IsEof(DAB_string) then
        error if true, "Corrupt file: " * filename;
    end if;
    return StringToIntegerSequence(DAB_string);
end intrinsic;

intrinsic ClassInvariants(Dat::DBUser,chi::RngUPolElt) -> SeqEnum, SeqEnum
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, returns the sequence of abelian invariants of the
    maximal order, followed by the invariants of the narrow class group of the
    real quadratic subfield.}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of ordinary curves.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    require IsIrreducible(chi) : "Argument 2 must be irreducible.";
    bool, filename := ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    require bool : "Argument 1 contains no data file for this Frobenius characteristic polynomial.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    // 1. [1] the quartic CM field invariants D, A, B;
    _ := Gets(file); // DAB
    // 2. [1] the type of quartic CM field:
    _ := Gets(file); // t
    // 3. [1] the class group abelian invariants of O_K [ h1_i ];
    h1_invs := StringToIntegerSequence(Gets(file));
    // 4. [1] the narrow class group abelian invariants of O_F [ h2_i ];
    h2_invs := StringToIntegerSequence(Gets(file));
    delete file;
    return h1_invs, h2_invs;
end intrinsic;

intrinsic ClassNumber(Dat::DBUser,chi::RngUPolElt) -> RngIntElt, RngIntElt
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, returns the class number of the maximal order,
    followed by the narrow class number of the real quadratic subfield.}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of ordinary curves.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    require IsIrreducible(chi) : "Argument 2 must be irreducible.";
    bool, filename := ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    require bool : "Argument 1 contains no data file for this Frobenius characteristic polynomial.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    // 1. [1] the quartic CM field invariants D, A, B;
    _ := Gets(file); // DAB
    // 2. [1] the type of quartic CM field:
    _ := Gets(file); // t
    // 3. [1] the class group abelian invariants of O_K [ h1_i ];
    h1_invs := StringToIntegerSequence(Gets(file));
    // 4. [1] the narrow class group abelian invariants of O_F [ h2_i ];
    h2_invs := StringToIntegerSequence(Gets(file));
    delete file;
    return &*h1_invs, &*h2_invs;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function Genus2CurvesFilename(p,r,s1,s2)
    prmstg := pad_int(p,prime_len);
    expstg := pad_int(r,prime_exp);
    s1stg := pad_int(s1,symm1_len);
    s2stg := pad_int(s2,symm2_len);
    if System("test -d " * DATDIR) ne 0 then
        System(&*[ "mkdir ", DATDIR]);
    end if;
    dirpath := DATDIR * prmstg * "^" * expstg * "/";
    filename := &*[ dirpath, "crvg2.", s1stg, ".", s2stg, ".db" ];
    return filename, dirpath;
end function;

function IsInGenus2CurvesDomain(X)
    case ExtendedType(X):
    when CrvHyp[FldFin]:
        return Genus(X) eq 2, "Argument must be a genus 2 curve.";
            "Argument must be a Frobenius characteristic polynomial, " *
            "genus 2 curve, sequence of Igusa invariants, or tuple of length 4";
    when RngUPolElt[RngInt]:
        bool := IsValidFrobeniusCharpoly(X,2);
        if not bool then
            x := Parent(X).1;
            bool := IsValidFrobeniusCharpoly(Evaluate(X,-x),2);
        end if;
        if not bool then
            return false,
                "Argument must be a Frobenius characteristic polynomial, " *
                "genus 2 curve, sequence of Igusa invariants, or tuple of length 4";
        end if;
    when RngUPolElt[FldRat]:
        bool := IsValidFrobeniusCharpoly(X,2);
        if not bool then
            x := Parent(X).1;
            bool := IsValidFrobeniusCharpoly(Evaluate(X,-x),2);
        end if;
        if not bool then
            return false,
                "Argument must be a Frobenius characteristic polynomial, " *
                "genus 2 curve, sequence of Igusa invariants, or tuple of length 4";
        end if;
    when SeqEnum[FldFinElt]:
        if #X notin {5,10} then
            return false,
                "Argument must be a Frobenius characteristic polynomial, " *
                "genus 2 curve, sequence of Igusa invariants, or tuple of length 4";
        end if;
    else
        if Type(X) ne Tup or #X ne 3 then
            return false,
                "Argument must be a Frobenius characteristic polynomial, " *
                "genus 2 curve, sequence of Igusa invariants, or tuple of length 4";
        end if;
        // X := <p,r,[s1,s2]>
        if not IsPrime(X[1]) and X[2] ge 1 then
            return false, "Argument must define a Frobenius characteristic polynoomial.";
        end if;
        if ExtendedType(X[3]) ne SeqEnum[RngIntElt] or #X[3] ne 2 then
            return false, "Argument component 3 must be a sequence of two integers.";
        end if;
        // s1, s2 := Explode(X[3]);
        if ExtendedType(X[4]) ne SeqEnum[RngIntElt] or #X[4] gt 2 then
            return false, "Argument component 4 must be a sequence of at most two integers.";
        end if;
    end case;
    return true, "";
end function;

function ExistsGenus2CurvesObject(X)
    if Type(X) eq RngUPolElt then
        return ExistsGenus2CurvesDataFile(X);
    end if;
    // The remaining possibilities for X are a CrvHyp or Igusa invariants
    if Type(X) eq CrvHyp then
        if Genus(X) ne 2 or Type(BaseRing(X)) ne FldFin then
            return false, "";
        end if;
        JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(X));
        chi := FrobeniusCharacteristicPolynomial(X);
    else
        if #X eq 5 then
            JJ := IgusaToNormalizedIgusaInvariants(X);
            C := HyperellipticCurveFromIgusaInvariants(JJ);
            chi := FrobeniusCharacteristicPolynomial(C);
        else
            C := HyperellipticCurveFromAbsoluteIgusaInvariants(X);
            JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
            chi := FrobeniusCharacteristicPolynomial(C);
        end if;
    end if;
    bool, filename := ExistsGenus2CurvesDataFile(X);
    if not bool then
        return false, filename;
    end if;
    FF := Universe(JJ);
    p := Characteristic(FF);
    r := Degree(FF);
    // Read the file:
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    // 1. [1] the quartic CM field invariants D, A, B;
    DAB := StringToIntegerSequence(Gets(file));
    // 2. [1] the type of quartic CM field:
    t := StringToInteger(Gets(file));
    // 3. [1] the class group abelian invariants of O_K [ h1_i ];
    h1_invs := StringToIntegerSequence(Gets(file));
    // 4. [1] the narrow class group abelian invariants of O_F [ h2_i ];
    h2_invs := StringToIntegerSequence(Gets(file));
    // 5. [1] the abelian group invariants of O_K/\ZZ[\pi,\bar\pi];
    condK := StringToIntegerSequence(Gets(file));
    while 1 in condK do Remove(~condK,1); end while;
    // 6. [1] the abelian group invariants of O_F/O_F \cap \ZZ[\pi,\bar\pi];
    condF := StringToIntegerSequence(Gets(file));
    while 1 in condF do Remove(~condF,1); end while;
    // 7. [4] the basis matrix for O_K in terms of the power basis for \QQ(\pi).
    M := [];
    for i in [1..4] do
        Append(~M,StringToIntegerSequence(Gets(file)));
    end for;
    // 8. Finite field data:
    cffs := StringToIntegerSequence(Gets(file));
    while true do
        condO_string := Gets(file);
        if IsEof(condO_string) then break; end if;
        // 9. for each endomorphism ring O in \ZZ[\pi,\bar\pi] \subseteq O \subseteq O_K:
        //   a. [1] the abelian group invariants of O_K/O;
        condO := StringToIntegerSequence(condO_string);
        while 1 in condO do Remove(~condO,1); end while;
        if condO ne [0] then
            //   b. [1] the abelian group invariants of O_F/(O \cup O_F);
            condR := StringToIntegerSequence(Gets(file));
            while 1 in condR do Remove(~condR,1); end while;
            //   c. [4] the integral basis matrix of O in O_K;
            MO := [];
            for i in [1..4] do
                Append(~MO,StringToIntegerSequence(Gets(file)));
            end for;
            MO := Matrix(MO);
        end if;
        //   d. [1] the number of invariants known = n
        num := StringToInteger(Gets(file));
        //  e. [1] times num:
        //         the concatenated sequence of five normalized Igusa invariants
        for i in [1..num] do
            JJ_cat := StringToIntegerSequence(Gets(file));
            if JJ eq [ FF!JJ_cat[[r*i+1..r*(i+1)]] : i in [0..4] ] then
                return true, filename;
            end if;
        end for;
    end while;
    delete file;
    return false, filename;
end function;

function ExistsGenus2CurvesDataFile(X)
    // Returns true if and only if the compressed data file exists,
    // and if so, returns the file handle for reading.
    if Type(X) eq SeqEnum then
        if Type(Universe(X)) ne FldFin or #X notin {5,10} then
            return false, "";
        end if;
        if #X eq 5 then
            X := HyperellipticCurveFromIgusaInvariants(X);
        else
            X := HyperellipticCurveFromAbsoluteIgusaInvariants(X);
        end if;
    end if;
    if Type(X) eq CrvHyp then
        if Genus(X) ne 2 or Type(BaseRing(X)) ne FldFin then
            return false, "";
        end if;
        X := FrobeniusCharacteristicPolynomial(X);
    end if;
    if Type(X) eq RngUPolElt then
        cc := Eltseq(X);
        if Type(Universe(cc)) eq FldRat then
            cc := ChangeUniverse(cc,IntegerRing());
        end if;
        s1 := Abs(cc[4]); s2 := cc[3]; q := cc[1];
        bool, p, r := IsPrimePower(q); assert bool;
        n := r div 2; q := p^n;
        assert r mod 2 eq 0 and Abs(cc[2]) eq q*s1 and cc[5] eq 1;
        X := <p,n,[s1,s2]>;
    end if;
    if Type(X) ne Tup or #X ne 3 then
        return false, "";
    end if;
    p := X[1]; n := X[2]; s1, s2 := Explode(X[3]);
    filename, dirpath := Genus2CurvesFilename(p,n,Abs(s1),s2);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function Genus2CurvesDataFile(p,n,s1,s2)
    filename, dirpath := Genus2CurvesFilename(p,n,s1,s2);
    if System("test -d " * dirpath) ne 0 then
        System(&*[ "mkdir ", dirpath]);
    end if;
    return filename;
end function;

//////////////////////////////////////////////////////////////////////////////

function QuarticCMInvariants(chi) // -> SeqEnum, RngIntElt, RngIntElt
    facts := Factorization(chi);
    if #facts eq 1 and facts[1][2] eq 1 then
        K := NumberField(chi);
        DAB := QuarticCMFieldInvariants(K);
        type_invs := QuarticCMFieldType(K);
        case type_invs:
        when [2,2]:
            t := 0;
        when [4]:
            t := 1;
        when [8]:
            t := 2;
        end case;
        h1_invs := CMFieldClassInvariants(K);
        F := QuadraticField(DAB[1]);
        h2_invs := AbelianInvariants(NarrowClassGroup(F));
    elif #facts eq 1 and facts[1][2] eq 2 then
        // chi is the square of a quadratic polynomial
        D1 := FundamentalDiscriminant(Discriminant(facts[1][1]));
        DAB := [1,0,D1]; t := 0;
        K1 := QuadraticField(D1);
        h1_invs := AbelianInvariants(ClassGroup(K1));
        h2_invs := [];
    elif #facts eq 1 and facts[1][2] eq 4 then
        // chi is the fourth power of a linear polynomial
        DAB := [1,1,1]; t := 0;
        h1_invs := [];
        h2_invs := [];
    elif #facts eq 2 and &and[ f[2] eq 1 : f in facts ] then
        // chi is the product of two quadratic polynomials
        D1 := FundamentalDiscriminant(Discriminant(facts[1][1]));
        D2 := FundamentalDiscriminant(Discriminant(facts[2][1]));
        if D1 lt D2 then
            D1, D2 := Explode([D2,D1]);
        end if;
        DAB := [1,D1,D2]; t := 0;
        K1 := QuadraticField(D1);
        h1_invs := AbelianInvariants(ClassGroup(K1));
        K2 := QuadraticField(D2);
        h2_invs := AbelianInvariants(ClassGroup(K2));
    elif #facts eq 2 and facts[1][2] eq 2 and facts[1][2] eq 1 then
        D1 := 1;
        D2 := FundamentalDiscriminant(Discriminant(facts[2][1]));
        DAB := [1,1,1]; t := 0;
        K1 := QuadraticField(D1);
        h1_invs := AbelianInvariants(ClassGroup(K1));
        h2_invs := [];
    elif #facts eq 2 and &and[ f[2] eq 2 : f in facts ] then
        // chi = (x-q)^2*(x+q)^2
        DAB := [1,1,1]; t := 0;
        h1_invs := [];
        h2_invs := [];
    else
        assert false;
    end if;
    if #h1_invs eq 0 then
        h1_invs := [1];
    end if;
    if #h2_invs eq 0 then
        h2_invs := [1];
    end if;
    return DAB, t, h1_invs, h2_invs;
end function;

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure Genus2CurvesSequencesWrite(chi,
    IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq)

    PZ := PolynomialRing(IntegerRing());
    K := NumberField(chi);
    OK := MaximalOrder(K);
    chi := PZ!DefiningPolynomial(K);
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2); assert bool;
    s1 := Abs(cc[4]); s2 := cc[3];
    hash := Sprint(Hash(Cputime()));
    filename := Genus2CurvesDataFile(p,r,s1,s2);
    System("touch " * filename * "." * hash);
    file := Open(filename * "." * hash,"w"); Flush(file);
    MatQQ := MatrixAlgebra(RationalField(),4);
    MatZZ := MatrixAlgebra(IntegerRing(),4);
    MK := BasisMatrix(OK);
    den := LCM([ Denominator(c) : c in Eltseq(MK) ]);
    MK := MatQQ!EchelonForm(MatZZ!(den*MK))/den;
    if #IgusaInvariants_seqs eq 0 then
        FF := FiniteField(p,r);
    else
        FF := Universe(IgusaInvariants_seqs[1][1]);
    end if;
    DAB, t, h1_invs, h2_invs := QuarticCMInvariants(chi);
    /*
        Let K = Q[x]/(x^4+Ax^2+B) where m^2D = A^2-4B, determined by
        the Frobenius characteristic polynomial chi, and F its real
        quadratic subfield.
          1. [1] the quartic CM field invariants D, A, B;
                 * this must be extended when chi is not irreducible, setting
                   D = 1 and A = disc(D1), B = disc(D2) where D1 and D2 are
                   the discriminants of the quadratic factors.
          2. [1] the type of quartic CM field:
                   0 = biquadratic C2xC2,
                   1 = cyclic C4,
                   2 = non-normmal dihedral D4;
          3. [1] the class group abelian invariants of O_K [ h1_i ];
          4. [1] the narrow class group abelian invariants of O_F [ h2_i ];
          5. [1] the abelian group invariants of O_K/\ZZ[\pi,\bar\pi];
          6. [1] the abelian group invariants of O_F/O_F \cap \ZZ[\pi,\bar\pi];
          7. [4] the basis matrix for O_K in terms of the power basis for \QQ(\pi).
          8. the coefficients of the minimal polynomial of \FF_{p^r}.
          9. for each endomorphism ring O in \ZZ[\pi,\bar\pi] \subseteq O \subseteq O_K:
             a. [1] the abelian group invariants of O_K/O;
             b. [1] the abelian group invariants of O_F/(O \cup O_F);
             c. [4] the integral basis matrix of O in O_K;
             d. [1] the number of invariants known = n
             e. [1] times n:
                    the concatenated sequence of five normalized Igusa invariants
          X. for any unclassified endomorphism ring we record:
             a. [1] the fake abelian group invariants [ 0 ]
             b. [1] the number of invariants known = n
             c. [1] times n:
                    the concatenated sequence of five normalized Igusa invariants

        If the Frobenius charpoly is irreducible then #2 consists of the pair of
        class group abelian invariants of K and its real subfield F, otherwise
        is the pair of class group abelian invariants for disc(K1) and disc(K2).

        If the Frobenius charpoly is reducible then 5.-8. are omitted as irrelevant.
    */
    // 1. [1] the quartic CM field invariants D, A, B;
    Puts(file,&*[ Sprint(x) * " " : x in DAB ]);
    // 2. [1] the type of quartic CM field:
    Puts(file,Sprint(t));
    // 3. [1] the class group abelian invariants of O_K [ h1_i ];
    Puts(file,&*[ Sprint(x) * " " : x in h1_invs ]);
    // 4. [1] the narrow class group abelian invariants of O_F [ h2_i ];
    Puts(file,&*[ Sprint(x) * " " : x in h2_invs ]);
    if IsIrreducible(chi) then
        // 5. [1] the abelian group invariants of O_K/\ZZ[\pi,\bar\pi];
        cond1 := FrobeniusVerschiebungConductorAbelianInvariants(chi);
        if #cond1 eq 0 then
            Puts(file,"1");
        else
            Puts(file,&*[ Sprint(x) * " " : x in cond1 ]);
        end if;
        // 6. [1] the abelian group invariants of O_F/O_F \cap \ZZ[\pi,\bar\pi];
        cond2 := FrobeniusVerschiebungRealSubringConductorAbelianInvariants(chi);
        if #cond2 eq 0 then
            Puts(file,"1");
        else
            Puts(file,&*[ Sprint(x) * " " : x in cond2 ]);
        end if;
        K := NumberField(chi);
        cconj := ComplexConjugation(K);
        // 7. [4] the basis matrix for O_K in terms of the power basis for \QQ(\pi).
        for i in [1..4] do
            v := Eltseq(MK[i]) cat [1];
            m := LCM([ Denominator(a) : a in v ]);
            Puts(file,&*[ Sprint(a*m) * " " : a in v ]);
        end for;
    else
        assert false;
    end if;
    // 8. Finite field data:
    f := DefiningPolynomial(FF);
    Puts(file,&*[ Sprint(a) * " " : a in Eltseq(f) ]);
    // 9. for each endomorphism ring O in \ZZ[\pi,\bar\pi] \subseteq O \subseteq O_K:
    num := #IgusaInvariants_seqs;
    for i in [1..num] do
        MO := OrdersBasis_seq[i];
        // a. [1] the abelian group invariants of O_K/O;
        condO := Conductors_seq[i];
        if #condO eq 0 then
            Puts(file,"1"); // or empty line for empty sequence
        else
            Puts(file,&*[ Sprint(c) * " " : c in condO ]);
        end if;
        // b. [1] the abelian group invariants of O_F/(O \cup O_F);
        condR := RealConductors_seq[i];
        if #condR eq 0 then
            Puts(file,"1"); // or empty line for empty sequence
        else
            Puts(file,&*[ Sprint(c) * " " : c in condR ]);
        end if;
        // c. [4] the integral basis matrix of O in O_K;
        for j in [1..4] do
            Puts(file,&*[ Sprint(c) * " " : c in Eltseq(MO[j]) ]);
        end for;
        JJ_seq := IgusaInvariants_seqs[i];
        // d. [1] the number of invariants known = n
        Puts(file,Sprint(#JJ_seq));
        // e. [1] times n:
        //    the concatenated sequence of five normalized Igusa invariants
        for JJ in JJ_seq do
            Puts(file,&*[ &*[ Sprint(a) * " " : a in Eltseq(c) ] : c in JJ ]);
        end for;
    end for;
    delete file;
    // System("bzip2 -c " * filename * "." * hash * " > " * filename * "z." * hash * "; wait");
    // System("chmod a+r " * filename * "z." * hash);
    // System("mv " * filename * "z." * hash * " " * filename * "z");
    for i in [1..4] do
        t := System("bzip2 " * filename * "." * hash * "; wait");
        if t ne 0 then
            print "Failed: bzip2 " * filename * "." * hash;
        else
            break;
        end if;
    end for;
    System("chmod a+r " * filename * "." * hash * ".bz2");
    System("mv " * filename * "." * hash * ".bz2 " * filename * "z");
end procedure;

procedure Genus2CurvesWrite(chi,curve)
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
        error if not bool,
            "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
        if Type(curve) eq CrvHyp then
            curve := QuadraticTwist(curve);
        elif Type(curve) eq Tup then
            error if Type(curve[2]) ne RngOrd,
                "Argument 3 must be a curve, tuple consisting of a curve and endomorphism ring, or sequence thereof.";
            if ExtendedType(curve[1]) eq SeqEnum[FldFinElt] then
                if #curve[1] eq 5 then
                    C := HyperellipticCurveFromIgusaInvariants(curve[1]);
                elif #curve[1] eq 10 then
                    C := HyperellipticCurveFromAbsoluteIgusaInvariants(curve[1]);
                else
                    error if true,
                        "Argument 3 must be a curve, tuple consisting of a curve and endomorphism ring, or sequence thereof.";
                end if;
                curve := <C,curve[2]>;
            end if;
            error if ExtendedType(curve[1]) ne CrvHyp[FldFin],
                "Argument 3 must be a curve, tuple consisting of a curve and endomorphism ring, or sequence thereof.";
            curve[1] := QuadraticTwist(curve[1]);
            K := NumberField(curve[2]);
            f := DefiningPolynomial(K);
            x := Parent(f).1;
            L := NumberField(Evaluate(f,-x));
            OL := MaximalOrder(L);
            m := hom< K->L | -L.1 >;
            O := sub< OL | [ m(K!a) : a in Basis(curve[2]) ] >;
            curve[2] := O;
        elif not (Type(curve) eq SeqEnum and #curve eq 0) then
            error if true,
                "Argument 3 must be a curve, tuple consisting of a curve and endomorphism ring, or sequence thereof.";
        end if;
    end if;
    s1 := Abs(cc[4]); s2 := cc[3];
    DBZ2 := Genus2ZetaFunctionsDatabase();
    if ExtendedType(curve) eq CrvHyp[FldFin] then
        C := curve;
        if FrobeniusCharacteristicPolynomial(C) ne chi then
            C := QuadraticTwist(C);
        end if;
        assert FrobeniusCharacteristicPolynomial(C) eq chi;
        Write(DBZ2,chi,C : Overwrite);
        O := EndomorphismRing(Jacobian(C));
    elif Type(curve) eq Tup then
        error if not (Type(curve[1]) eq CrvHyp and Type(curve[2]) eq RngOrd),
            "Argument 3 must be a curve, tuple consisting of a curve and endomorphism ring, or sequence thereof.";
        C := curve[1];
        assert FrobeniusCharacteristicPolynomial(C) eq chi;
        Write(DBZ2,chi,C : Overwrite);
        O := curve[2];
    elif ExtendedType(curve) eq SeqEnum[FldFinElt] then
        if #curve eq 5 then
            C := HyperellipticCurveFromIgusaInvariants(curve);
        elif #curve eq 10 then
            C := HyperellipticCurveFromAbsoluteIgusaInvariants(curve);
        else
            error if true, "Argument 3 must be a curve, tuple consisting of a curve and endomorphism ring, or sequence thereof.";
        end if;
        if FrobeniusCharacteristicPolynomial(C) ne chi then
            C := QuadraticTwist(C);
        end if;
        assert FrobeniusCharacteristicPolynomial(C) eq chi;
        Write(DBZ2,chi,C : Overwrite);
        O := EndomorphismRing(Jacobian(C));
    elif Type(curve) eq SeqEnum and #curve eq 0 then
        Write(DBZ2,chi,curve : Overwrite);
        if not ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) then
            IgusaInvariants_seqs := [ ];
            OrdersBasis_seq := [ ];
            Conductors_seq := [ ];
            RealConductors_seq := [ ];
            print "  Writing void invariants to disk.";
            Genus2CurvesSequencesWrite(chi, IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq);
        end if;
        return;
    elif ExtendedType(curve) eq SeqEnum[CrvHyp] then
        for C in curve do
            Genus2CurvesWrite(chi,curve);
        end for;
        return;
    elif ExtendedType(curve) eq SeqEnum[SeqEnum[FldFinElt]] then
        for C in curve do
            Genus2CurvesWrite(chi,curve);
        end for;
        return;
    else
        error if true, "Argument 3 must be a curve, tuple consisting of a curve and endomorphism ring, or sequence thereof.";
    end if;
    xi := FrobeniusCharacteristicPolynomial(C);
    error if xi ne chi,
        "Argument 2 must be the Frobenius characteristic polynomial of Argument 3.";
    JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
    s := LCM([ Degree(MinimalPolynomial(jj)) : jj in JJ ]);
    if s ne r then
        vprintf Genus2Curves: "  Igusa invariants defined over smaller field of degree %o.\n", s;
        JJ := ChangeUniverse(JJ,FiniteField(p,s));
        C := HyperellipticCurveFromIgusaInvariants(JJ);
        chi := FrobeniusCharacteristicPolynomial(C);
        if Coefficient(chi,3) gt 0 then
            C := QuadraticTwist(C);
            chi := FrobeniusCharacteristicPolynomial(C);
        end if;
        DBG2 := Genus2CurvesDatabase();
        Write(DBG2,chi,C : Overwrite);
        return;
    end if;
    JJ_seq := [ [ ji^p^k : ji in JJ ] : k in [0..r-1] ];
    deg := #SequenceToSet(JJ_seq);
    error if deg ne r, "Argument 2 is defined over subfield of degree " * Sprint(deg);
    error if not IsIrreducible(chi), "Argument 2 must be irreducible.";
    MatQQ := MatrixAlgebra(RationalField(),4);
    MatZZ := MatrixAlgebra(IntegerRing(),4);
    K := NumberField(O);
    OK := MaximalOrder(K);
    if not DefiningPolynomial(K) eq chi then
        print "chi:", chi;
        print "K:", K;
        error if true, "Curve and endomorphism ring arguments are not compatible.";
    end if;
    MK := BasisMatrix(OK);
    den := LCM([ Denominator(c) : c in Eltseq(MK) ]);
    MK := MatQQ!EchelonForm(MatZZ!(den*MK))/den;
    baseO := EchelonForm(MatZZ!(BasisMatrix(O)*MK^-1));
    condO := ConductorAbelianInvariants(O);
    condR := RealSubringConductorAbelianInvariants(O);
    flag := true;
    if not ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) then
        IgusaInvariants_seqs := [ JJ_seq ];
        OrdersBasis_seq := [ baseO ];
        Conductors_seq := [ condO ];
        RealConductors_seq := [ condR ];
    else
        DBG2 := Genus2CurvesDatabase();
        IgusaInvariants_seqs, Orders_seq,
            Conductors_seq, RealConductors_seq := IgusaInvariantsSequences(DBG2,chi);
        OrdersBasis_seq := [ EchelonForm(MatZZ!(BasisMatrix(O)*MK^-1)) : O in Orders_seq ];
        i := Index(OrdersBasis_seq,baseO);
        if i eq 0 then
            Append(~IgusaInvariants_seqs,JJ_seq);
            Append(~OrdersBasis_seq,baseO);
            Append(~Conductors_seq,condO);
            Append(~RealConductors_seq,condR);
            i := #IgusaInvariants_seqs;
        elif JJ notin IgusaInvariants_seqs[i] then
            IgusaInvariants_seqs[i] cat:= JJ_seq;
            Conductors_seq[i] := condO;
            RealConductors_seq[i] := condR;
        else
            flag := false;
            Conductors_seq[i] := condO;
            RealConductors_seq[i] := condR;
        end if;
        // Either the curve is new, or we arrive here with the curve
        // and endomorphism ring specified.  If the curve was written
        // to another index (with different endomorphism ring) then
        // we assume the intend is to rewrite it to a new, corrected
        // endomorphism ring.  Therefore we remove the other copy.
        j := 1;
        while j le #IgusaInvariants_seqs do
            if i eq j then j +:= 1; continue; end if;
            if JJ in IgusaInvariants_seqs[j] then
                flag := true;
                print "  Removing invariants from conductor", Conductors_seq[j];
                for Ji in JJ_seq do
                    Exclude(~IgusaInvariants_seqs[j],Ji);
                end for;
                if #IgusaInvariants_seqs[j] eq 0 then
                    Remove(~IgusaInvariants_seqs,j);
                    Remove(~OrdersBasis_seq,j);
                    Remove(~Conductors_seq,j);
                    Remove(~RealConductors_seq,j);
                    if j lt i then i -:= 1; end if;
                    j -:= 1;
                end if;
            end if;
            j +:= 1;
        end while;
        /*
        Sort the sequence of invariants according to the conductor indices,
        and set flag to overwrite if the sequence wasn't already sorted:
        */
        n := #Conductors_seq;
        if n gt 1 then
            pi := SortConductorSequences(Conductors_seq,RealConductors_seq);
            if pi ne Parent(pi)!1 then
                IgusaInvariants_seqs := [ IgusaInvariants_seqs[i^pi] : i in [1..n] ];
                OrdersBasis_seq := [ OrdersBasis_seq[i^pi] : i in [1..n] ];
                Conductors_seq := [ Conductors_seq[i^pi] : i in [1..n] ];
                RealConductors_seq := [ RealConductors_seq[i^pi] : i in [1..n] ];
                flag := true;
            end if;
        end if;
    end if;
    if not flag then return; end if;
    printf "  Writing new invariants to disk (cond = %o).\n", condO;
    Genus2CurvesSequencesWrite(chi, IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq);
end procedure;

procedure Genus2CurvesDelete(chi,curve)
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
        if Type(curve) eq CrvHyp then
            curve := QuadraticTwist(curve);
        elif Type(curve) eq Tup then
            error if Type(curve[1]) ne CrvHyp or Type(curve[2]) ne RngOrd,
                "Argument 2 must be a tuple consisting of a curve and endomorphism ring.";
            curve[1] := QuadraticTwist(curve[1]);
            K := NumberField(curve[2]);
            f := DefiningPolynomial(K);
            x := Parent(f).1;
            L := NumberField(Evaluate(f,-x));
            OL := MaximalOrder(L);
            m := hom< K->L | -L.1 >;
            O := sub< OL | [ m(K!a) : a in Basis(curve[2]) ] >;
            curve[2] := O;
        end if;
    end if;
    error if not bool,
        "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    s1 := Abs(cc[4]); s2 := cc[3];
    if Type(curve) eq Tup then
        error if not (Type(curve[1]) eq CrvHyp and Type(curve[2]) eq RngOrd),
            "Argument 2 must be a tuple consisting of a curve and endomorphism ring.";
        C := curve[1];
        O := curve[2];
    else
        error if true,
            "Argument 2 must be a tuple consisting of a curve and order.";
    end if;
    xi := FrobeniusCharacteristicPolynomial(C);
    if xi eq Evaluate(chi,-Parent(chi).1) then
        C := QuadraticTwist(C);
    elif xi ne chi then
        error if false,
            "Argument 2 must be the Frobenius characteristic polynomial of Argument 3.";
    end if;
    JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
    if LCM([ Degree(MinimalPolynomial(jj)) : jj in JJ ]) ne r then return; end if;
    JJ_seq := [ [ ji^p^k : ji in JJ ] : k in [0..r-1] ];
    deg := #SequenceToSet(JJ_seq);
    error if deg ne r, "Argument 2 is defined over subfield of degree " * Sprint(deg);
    error if not IsIrreducible(chi), "Argument 2 must be irreducible.";
    MatQQ := MatrixAlgebra(RationalField(),4);
    MatZZ := MatrixAlgebra(IntegerRing(),4);
    K := NumberField(O);
    OK := MaximalOrder(K);
    if not DefiningPolynomial(K) eq chi then
        print "chi:", chi;
        print "K:", K;
        error if true, "Curve and endomorphism ring arguments are not compatible.";
    end if;
    MK := BasisMatrix(OK);
    den := LCM([ Denominator(c) : c in Eltseq(MK) ]);
    MK := MatQQ!EchelonForm(MatZZ!(den*MK))/den;
    baseO := EchelonForm(MatZZ!(BasisMatrix(O)*MK^-1));
    condO := ConductorAbelianInvariants(O);
    condR := RealSubringConductorAbelianInvariants(O);
    flag := true;
    if not ExistsGenus2CurvesDataFile(<p,r,[s1,s2]>) then return; end if;
    DBG2 := Genus2CurvesDatabase();
    IgusaInvariants_seqs, Orders_seq,
        Conductors_seq, RealConductors_seq := IgusaInvariantsSequences(DBG2,chi);
    OrdersBasis_seq := [ EchelonForm(MatZZ!(BasisMatrix(O)*MK^-1)) : O in Orders_seq ];
    i := Index(OrdersBasis_seq,baseO);
    if i eq 0 then return; end if;
    j := Index(IgusaInvariants_seqs[i],JJ);
    if j eq 0 then return; end if;
    /*
    Sort the sequence of invariants according to the conductor indices,
    and set flag to overwrite if the sequence wasn't already sorted:
    */
    n := #Conductors_seq;
    if #IgusaInvariants_seqs[i] eq r then
        Remove(~IgusaInvariants_seqs,i);
        Remove(~OrdersBasis_seq,i);
        Remove(~Conductors_seq,i);
        Remove(~RealConductors_seq,i);
    else
        for k in [0..r-1] do
            Exclude(~IgusaInvariants_seqs[i],[ ji^p^k : ji in JJ ]);
        end for;
    end if;
    n := #Conductors_seq;
    if n gt 1 then
        pi := SortConductorSequences(Conductors_seq,RealConductors_seq);
        if pi ne Parent(pi)!1 then
            IgusaInvariants_seqs := [ IgusaInvariants_seqs[i^pi] : i in [1..n] ];
            OrdersBasis_seq := [ OrdersBasis_seq[i^pi] : i in [1..n] ];
            Conductors_seq := [ Conductors_seq[i^pi] : i in [1..n] ];
            RealConductors_seq := [ RealConductors_seq[i^pi] : i in [1..n] ];
        end if;
    end if;
    print "  Deleting invariants from disk.";
    Genus2CurvesSequencesWrite(chi, IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            SORT FUNCTION                                 //
//////////////////////////////////////////////////////////////////////////////

function SortConductorSequences(Conductors,RealConductors)
    n := #Conductors;
    assert n eq #RealConductors;
    Cond_rev := [ Reverse(cond) : cond in Conductors ];
    RealCond_rev := [ Reverse(cond) : cond in RealConductors ];
    G := Sym(n);
    id := Id(G); pi := id;
    Sort(~RealCond_rev,~pi);
    Cond_rev := [ Cond_rev[i^pi] : i in [1..n] ];
    n1 := 1;
    while n1 lt n do
        c1 := RealCond_rev[n1];
        n2 := Max([ i : i in [n1..n] | RealCond_rev[i] eq c1 ]);
        // Sorting yields the same real conductor on the interval [n1..n2]:
        assert &and[ RealCond_rev[i] eq c1 : i in [n1..n2] ];
        if n1 lt n2 then
            id := Id(Sym(n2-n1+1)); qi := id;
            Cond_rev_sub := Cond_rev[[n1..n2]];
            Sort(~Cond_rev_sub,~qi);
            // This is somewhat counterintuitive:
            // [ i^(pi2*pi1) : i in [1..14] ] == [i^pi1 : i in [1..14]][[j^pi2 : j in [1..14]]]
            // since the induced action on index sequences in on the left:
            // For pi(I) = [ i^pi : i in I ], gives (pi2*pi1)(I) = pi2(pi1(I)) where I = [1..14].
            pi := G!([1..n1-1] cat [ n1-1+i^qi : i in [1..n2-n1+1] ] cat [n2+1..n]) * pi;
        end if;
        n1 := n2+1;
    end while;
    return pi;
end function;

intrinsic IgusaInvariantsSequencesSort(Dat::DBUser,chi::RngUPolElt : Rewrite := false)
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, sorts the sequence of normalized Igusa invariants
    of curves with this characteristic polynomial.}
    require Dat`DBIdentifier eq "Genus 2 curves" : "Argument 1 must be the database of ordinary curves.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    require chi in Dat : "Argument 2 must be a Frobenius charpoly in the database of genus 2 curves.";
    IgusaInvariants_seqs, Orders_seq, Conductors_seq, RealConductors_seq := IgusaInvariantsSequences(Dat,chi);
    pi := SortConductorSequences(Conductors_seq,RealConductors_seq);
    if pi eq Parent(pi)!1 and not Rewrite then return; end if;
    n := #Conductors_seq;
    IgusaInvariants_seqs := [ IgusaInvariants_seqs[i^pi] : i in [1..n] ];
    Orders_seq := [ Orders_seq[i^pi] : i in [1..n] ];
    Conductors_seq := [ Conductors_seq[i^pi] : i in [1..n] ];
    RealConductors_seq := [ RealConductors_seq[i^pi] : i in [1..n] ];
    n := #Conductors_seq;
    MatQQ := MatrixAlgebra(RationalField(),4);
    MatZZ := MatrixAlgebra(IntegerRing(),4);
    OK := MaximalOrder(NumberField(Orders_seq[1]));
    MK := BasisMatrix(OK);
    den := LCM([ Denominator(c) : c in Eltseq(MK) ]);
    MK := MatQQ!EchelonForm(MatZZ!(den*MK))/den;
    OrdersBasis_seq := [ EchelonForm(MatZZ!(BasisMatrix(O)*MK^-1)) : O in Orders_seq ];
    printf "  Rewriting invariants to disk (with permutation = %o).\n", pi;
    Genus2CurvesSequencesWrite(chi, IgusaInvariants_seqs, OrdersBasis_seq, Conductors_seq, RealConductors_seq);
end intrinsic;

