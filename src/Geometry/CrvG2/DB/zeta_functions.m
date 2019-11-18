//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                 GENUS 2 ZETA FUNCTION DATABASE                           //
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

DATDIR := GetEchidnaDatabaseRoot() * "/ZetaG2/";
prime_len := 6;
prime_exp := 3;
symm1_len := 6;
symm2_len := 12;

//////////////////////////////////////////////////////////////////////////////

import "genus2_curves.m": IsValidFrobeniusCharpoly, QuarticCMInvariants;

//////////////////////////////////////////////////////////////////////////////

declare verbose Genus2ZetaFunctions, 2;

//////////////////////////////////////////////////////////////////////////////

forward Genus2ZetaFunctionsDataFile, Genus2ZetaFunctionsDelete, Genus2ZetaFunctionsWrite;
forward IsInGenus2ZetaFunctionsDomain, ExistsGenus2ZetaFunctionsObject, ExistsGenus2ZetaFunctionsDataFile;
forward Genus2ZetaFunctionsSequencesWrite, SortConductorSequences;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic Genus2ZetaFunctionsDatabase() -> DBUser
    {The database of ordinary genus 2 curves.}
    /*
    Caution: The ExistsFunction is used (and intended) to test whether a
    given object is in the database.  If the input is a Frobenius charpoly
    or quartic CM field invariants, then existence of the data file is
    the desired test.  If the input is a curve or Igusa invariants, then we
    actually need to test whether the representative is stored in the database.
    So ExistsFunction will be defined to be ExistsGenus2ZetaFunctionsObject, and this
    will wrap the call to ExistsGenus2ZetaFunctionsDataFile in the former cases and
    membership in that file otherwise.
    */
    Dat := HackobjCreateRaw(DBUser);
    Dat`DBIdentifier := "Genus 2 zeta functions";
    Dat`WriteFunction := Genus2ZetaFunctionsWrite;
    Dat`DeleteFunction := Genus2ZetaFunctionsDelete;
    Dat`ExistsFunction := ExistsGenus2ZetaFunctionsObject;
    Dat`IsInDomainFunction := IsInGenus2ZetaFunctionsDomain;
    return Dat;
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

intrinsic Genus2ZetaFunctionsFrobeniusCharacteristicPolynomials(
    Dat::DBUser,p::RngIntElt,r::RngIntElt) -> SeqEnum
    {The sequence of Frobenius characteristic polynomials for ordinary
    genus 2 curves over the field of p^r elements, represented in the
    database Dat.}
    require Dat`DBIdentifier eq "Genus 2 zeta functions" :
        "Argument 1 must be the database of genus 2 zeta functions.";
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

intrinsic Genus2ZetaFunctionsIgusaInvariantsSequence(Dat::DBUser,chi::RngUPolElt)
    -> SeqEnum, SeqEnum, SeqEnum, SeqEnum, SeqEnum, SeqEnum
    {Given the database of genus 2 zeta functions and a Frobenius characteristic polynomial
    represented in the database, returns the sequence of normalized Igusa invariants of
    curves with this characteristic polynomial.}

    require Dat`DBIdentifier eq "Genus 2 zeta functions" :
        "Argument 1 must be the database of genus 2 zeta functions.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2); assert bool;
    FF := FiniteField(p,r);
    bool, filename := ExistsGenus2ZetaFunctionsDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    /*
    require bool : "Argument 2 is not in the database of genus 2 zeta functions.";
    */
    if not bool then
	return [ Parent([ FF.1 ]) | ];
    end if;
    // TODO: What happens when chi is reducible???
    K := NumberField(chi);
    OK := MaximalOrder(K);
    O_FrobVer := sub< OK | K.1, p^r/K.1 >;
    IgusaInvariants_seq := [ ];
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
    // 7. the coefficients of the minimal polynomial of \FF_p^r.
    cffs := StringToIntegerSequence(Gets(file));
    if Eltseq(DefiningPolynomial(FF)) ne cffs then
        print "DAB:", DAB;
        print "Frobenius charpoly:", chi;
        print "Defining polynomial coeffs:", Eltseq(DefiningPolynomial(FF));
        print "Nondefault database coeffs:", cffs;
        error if true, "Database has non-default defining polynomial for finite field.";
    end if;
    // 8. Igusa invariants:
    //   a. [1] first the number of known invariants = n
    num := StringToInteger(Gets(file));
    //   b. [n] then the concatenated sequence of five normalized Igusa invariants
    for i in [1..num] do
	JJ_cat := StringToIntegerSequence(Gets(file));
	Append(~IgusaInvariants_seq,[ FF!JJ_cat[[r*j+1..r*(j+1)]] : j in [0..4] ]);
    end for;
    delete file;
    return IgusaInvariants_seq, condK, condF, DAB, t, h1_invs, h2_invs;
end intrinsic;

intrinsic Genus2ZetaFunctionsClassInvariants(Dat::DBUser,chi::RngUPolElt) -> SeqEnum, SeqEnum
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, returns the sequence of abelian invariants of the
    maximal order, followed by the invariants of the narrow class group of the
    real quadratic subfield.}
    require Dat`DBIdentifier eq "Genus 2 zeta functions" :
	"Argument 1 must be the database of genus 2 zeta functions.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    require IsIrreducible(chi) : "Argument 2 must be irreducible.";
    bool, filename := ExistsGenus2ZetaFunctionsDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    require bool : "Argument 1 contains no data file for this Frobenius characteristic polynomial.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    // 1. [1] the quartic CM field invariants D, A, B;
    DAB_string := Gets(file);
    if IsEof(DAB_string) then
	error if true, "Corrupt file: " * filename;
    end if;
    // 2. [1] the type of quartic CM field:
    _ := Gets(file); // t
    // 3. [1] the class group abelian invariants of O_K [ h1_i ];
    h1_invs := StringToIntegerSequence(Gets(file));
    // 4. [1] the narrow class group abelian invariants of O_F [ h2_i ];
    h2_invs := StringToIntegerSequence(Gets(file));
    delete file;
    return h1_invs, h2_invs;
end intrinsic;

intrinsic Genus2ZetaFunctionsClassNumber(Dat::DBUser,chi::RngUPolElt) -> RngIntElt, RngIntElt
    {Given the database of genus 2 curves and a Frobenius characteristic polynomial
    represented in the database, returns the class number of the maximal order,
    followed by the narrow class number of the real quadratic subfield.}
    require Dat`DBIdentifier eq "Genus 2 zeta functions" :
	"Argument 1 must be the database of genus 2 zeta functions.";
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    end if;
    require bool : "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    require IsIrreducible(chi) : "Argument 2 must be irreducible.";
    bool, filename := ExistsGenus2ZetaFunctionsDataFile(<p,r,[s1,s2]>) where s1 := Abs(cc[4]) where s2 := cc[3];
    require bool : "Argument 1 contains no data file for this Frobenius characteristic polynomial.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    // 1. [1] the quartic CM field invariants D, A, B;
    DAB_string := Gets(file);
    if IsEof(DAB_string) then
	error if true, "Corrupt file: " * filename;
    end if;
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

function Genus2ZetaFunctionsFilename(p,r,s1,s2)
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

function IsInGenus2ZetaFunctionsDomain(X)
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

function ExistsGenus2ZetaFunctionsObject(X)
    if Type(X) eq RngUPolElt then
        return ExistsGenus2ZetaFunctionsDataFile(X);
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
    bool, filename := ExistsGenus2ZetaFunctionsDataFile(X);
    if not bool then
        return false, filename;
    end if;
    FF := Universe(JJ);
    p := Characteristic(FF);
    r := Degree(FF);
    // Read the file:
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
    // 7. Finite field data:
    cffs := StringToIntegerSequence(Gets(file));
    // 8. Igusa invariants
    //   a. [1] first the number of known invariants = n
    num := StringToInteger(Gets(file));
    //   b. [n] then the concatenated sequence of five normalized Igusa invariants
    for i in [1..num] do
	JJ_cat := StringToIntegerSequence(Gets(file));
	if JJ eq [ FF!JJ_cat[[r*i+1..r*(i+1)]] : i in [0..4] ] then
	    return true, filename;
	end if;
    end for;
    delete file;
    return false, filename;
end function;

function ExistsGenus2ZetaFunctionsDataFile(X)
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
    filename, dirpath := Genus2ZetaFunctionsFilename(p,n,Abs(s1),s2);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function Genus2ZetaFunctionsDataFile(p,n,s1,s2)
    filename, dirpath := Genus2ZetaFunctionsFilename(p,n,s1,s2);
    if System("test -d " * dirpath) ne 0 then
        System(&*[ "mkdir ", dirpath]);
    end if;
    return filename;
end function;

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure Genus2ZetaFunctionsSequencesWrite(chi, IgusaInvariants_seq, condK, condF, DAB, t, h1_invs, h2_invs)
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2); assert bool;
    s1 := Abs(cc[4]); s2 := cc[3];
    hash := Sprint(Hash(Cputime()));
    filename := Genus2ZetaFunctionsDataFile(p,r,s1,s2);
    System("touch " * filename * "." * hash);
    file := Open(filename * "." * hash,"w"); Flush(file);
    FF := #IgusaInvariants_seq eq 0 select FiniteField(p,r) else Universe(IgusaInvariants_seq[1]);
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
          7. the coefficients of the minimal polynomial of \FF_{p^r}.
          8. Igusa invariants
             a. [1] the number of known invariants = n
             b. [n] the concatenated sequence of five normalized Igusa invariants

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
    assert IsIrreducible(chi);
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
    // 7. Finite field data:
    f := DefiningPolynomial(FF);
    Puts(file,&*[ Sprint(a) * " " : a in Eltseq(f) ]);
    // 8. Igusa invariants:
    //  a. [1] first the number of known invariants known = n
    Puts(file,Sprint(#IgusaInvariants_seq));
    //  b. [n] then the concatenated sequence of five normalized Igusa invariants
    for JJ in IgusaInvariants_seq do
	Puts(file,&*[ &*[ Sprint(a) * " " : a in Eltseq(c) ] : c in JJ ]);
    end for;
    delete file;
    //System("bzip2 -c " * filename * "." * hash * " > " * filename * "z." * hash * "; wait");
    //System("chmod a+r " * filename * "z." * hash);
    //System("mv " * filename * "z." * hash * " " * filename * "z");
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

procedure Genus2ZetaFunctionsWrite(chi,curve)
    chi := PolynomialRing(IntegerRing())!chi;
    bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
    if not bool then
        chi := Evaluate(chi,-Parent(chi).1);
        bool, p, r, cc := IsValidFrobeniusCharpoly(chi,2);
        if Type(curve) eq CrvHyp then
            curve := QuadraticTwist(curve);
        elif Type(curve) eq Tup then
            error if Type(curve[1]) ne CrvHyp or Type(curve[2]) ne RngOrd,
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
        end if;
    end if;
    error if not bool,
        "Argument 2 must be a normalized characteristic polynomial of Frobenius.";
    s1 := Abs(cc[4]); s2 := cc[3];
    if ExtendedType(curve) eq CrvHyp[FldFin] then
        C := curve;
	if FrobeniusCharacteristicPolynomial(C) ne chi then
	    C := QuadraticTwist(C);
	end if;
    elif ExtendedType(curve) eq SeqEnum[FldFinElt] then
	if #curve eq 5 then
	    C := HyperellipticCurveFromIgusaInvariants(curve);
	elif #curve eq 10 then
	    C := HyperellipticCurveFromAbsoluteIgusaInvariants(curve);
	else
	    error if true,
		"Argument 3 must be a curve, Igusa invariants, or a sequence thereof.";
	end if;
	if FrobeniusCharacteristicPolynomial(C) ne chi then
	    C := QuadraticTwist(C);
	end if;
    elif Type(curve) eq SeqEnum and #curve eq 0 then
	if not ExistsGenus2ZetaFunctionsDataFile(<p,r,[s1,s2]>) then
	    DAB, t, h1_invs, h2_invs := QuarticCMInvariants(chi);
	    condK := FrobeniusVerschiebungConductorAbelianInvariants(chi);
	    condF := FrobeniusVerschiebungRealSubringConductorAbelianInvariants(chi);
	    vprint Genus2ZetaFunctions : "  Writing void invariants to disk.";
	    Genus2ZetaFunctionsSequencesWrite(chi, [], condK, condF, DAB, t, h1_invs, h2_invs);
	end if;
	return;
    elif ExtendedType(curve) eq SeqEnum[CrvHyp] then
        for C in curve do
	    Genus2ZetaFunctionsWrite(chi,C);
	end for;
	return;
    elif ExtendedType(curve) eq SeqEnum[SeqEnum[FldFinElt]] then
        for C in curve do
	    Genus2ZetaFunctionsWrite(chi,C);
	end for;
	return;
    else
	error if true,
	    "Argument 3 must be a curve or sequence of thereof.";
    end if;
    xi := FrobeniusCharacteristicPolynomial(C);
    error if xi ne chi,
	"Argument 2 (= " * Sprint(chi) * ") must be the Frobenius characteristic polynomial (= " * Sprint(xi) * ") of Argument 3.";
    JJ := IgusaToNormalizedIgusaInvariants(IgusaInvariants(C));
    if LCM([ Degree(MinimalPolynomial(jj)) : jj in JJ ]) ne r then return; end if;
    error if not IsIrreducible(chi), "Argument 2 must be irreducible.";
    JJ_orbit := [ [ ji^p^k : ji in JJ ] : k in [0..r-1] ];
    deg := #SequenceToSet(JJ_orbit);
    error if deg ne r, "Argument 2 is defined over subfield of degree " * Sprint(deg);
    if not ExistsGenus2ZetaFunctionsDataFile(<p,r,[s1,s2]>) then
	IgusaInvariants_seq := JJ_orbit;
	DAB, t, h1_invs, h2_invs := QuarticCMInvariants(chi);
	condK := FrobeniusVerschiebungConductorAbelianInvariants(chi);
	condF := FrobeniusVerschiebungRealSubringConductorAbelianInvariants(chi);
    else
        DBZ2 := Genus2ZetaFunctionsDatabase();
	IgusaInvariants_seq, condK, condF, DAB, t, h1_invs, h2_invs := Genus2ZetaFunctionsIgusaInvariantsSequence(DBZ2,chi);
	if JJ in IgusaInvariants_seq then
	    return;
	end if;
	IgusaInvariants_seq cat:= JJ_orbit;
    end if;
    vprint Genus2ZetaFunctions : "  Writing new invariants to disk.";
    Genus2ZetaFunctionsSequencesWrite(chi, IgusaInvariants_seq, condK, condF, DAB, t, h1_invs, h2_invs);
end procedure;
