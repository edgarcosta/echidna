//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                           SEXTIC CM FIELDS                               //
//        Copyright (C) 2013 David Kohel <David.Kohel@univ-amu.fr>          //
//                                                                          //
//  Distributed under the terms of the GNU General Public License (GPL)     //
//                                                                          //
//                  http://www.gnu.org/licenses/                            //
//                                                                          //
//        All rights granted to distribute under the GPL, version 2,        //
//          or (at your option) any later version of the license.           //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

DATDIR := GetEchidnaDatabaseRoot() * "/FldCM/6/";
rdisc_len := 12;
rdisc1_len := 6;
rdisc2_len := 6;
symm1_len := 8;
symm2_len := 8;
symm3_len := 8;
class_len := 6;

//////////////////////////////////////////////////////////////////////////////

import "octic_cm_fields.m" : OcticCMFieldWrite;

//////////////////////////////////////////////////////////////////////////////

forward SexticCMFieldDataFile, SexticCMFieldWrite;
forward IsInSexticCMFieldDomain, ExistsSexticCMFieldDataFile;
forward SexticCMClassNumberDataFile, ExistsSexticCMClassNumberDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic SexticCMFieldDatabase() -> DBUser
    {The database of sextic CM fields.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Sextic CM fields";
    Dat`Invariant := 6;
    Dat`WriteFunction := SexticCMFieldWrite;
    Dat`ExistsFunction := ExistsSexticCMFieldDataFile;
    Dat`IsInDomainFunction := IsInSexticCMFieldDomain;
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

function IsValidDABC(DABC,i)
    if #DABC ne 4 then
        return false,
            Sprintf("Argument %o must be a sequence of four integers.",i);
    end if;
    D, A, B, C := Explode(DABC);
    bool := D mod 4 in {0,1} and D gt 1;
    error_string :=
        Sprintf("Argument %o, element 1, must be a positive discriminant.",i);
    if not bool then
        return bool, error_string;
    end if;
    for j in [2,3,4] do
        error_string := Sprintf("Argument %o, element %o, must be non-negative.",j,i);
        if not DABC[j] ge 0 then return bool, error_string; end if;
    end for;
    bool := A^2 - 3*B ge 0;
    error_string := Sprintf("Argument %o, elements 2 and 3, are not valid.",i);
    if not bool then return bool, error_string; end if;
    D2 := -4*A^3*C + A^2*B^2 + 18*A*B*C - 4*B^3 - 27*C^2;
    bool := D2 mod D eq 0 and IsSquare(D2 div D);
    error_string := Sprintf("Argument %o, elements 2 and 3, are not valid.",i);
    if not bool then return bool, error_string; end if;
    return true, "";
end function;

//////////////////////////////////////////////////////////////////////////////

function IntegerToTypeInvariants(t_invs)
    case t_invs:
    when 0:
        return [3,2];
    when 1:
        return [3,4];
    when 2:
        return [3,8];
    when 3:
        return [6,2];
    when 4:
        return [6,4];
    when 5:
        return [6,8];
    end case;
    error if true, "Invalid integer for type specification.";
end function;

function TypeInvariantsToInteger(t_invs)
    case t_invs:
    when [3,2]:
        return 0;
    when [3,4]:
        return 1;
    when [3,8]:
        return 2;
    when [6,2]:
        return 3;
    when [6,4]:
        return 4;
    when [6,8]:
        return 5;
    end case;
    error if true, "Invalid type specification.";
end function;

//////////////////////////////////////////////////////////////////////////////
// Access functions
//////////////////////////////////////////////////////////////////////////////

intrinsic SexticCMField(Dat::DBUser,Invs::[RngIntElt]) -> SeqEnum
    {Given an integer sequence Invs = [D,a,b,c] return the sextic CM field
    with defining polynomial x^6 + a*x^4 + b*x^2 + c. The following fields
    are automatically assigned:
    
    K`IsCMField,
    K`SexticCMFieldInvariants,
    K`SexticCMFieldType,
    K`TotallyRealSubfield,
    K`CMFieldClassInvariants.

    Note that D must be the discriminant of the defining polynomial x^3 + a*x^2
    + b*x + c for the totaly real subfield.}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(Invs,2); require bool : error_string;
    require Invs in Dat : "Argument 2 is not in database argument 1.";
    D, a, b, c := Explode(Invs);
    K := NumberField(Polynomial([c,0,b,0,a,0,1]));
    K`IsCMField := true;
    K`SexticCMFieldInvariants := Invs;
    K`SexticCMFieldType := SexticCMFieldType(Dat,Invs);
    K`TotallyRealSubfield := sub< K | K.1^2 >;
    K`CMFieldClassInvariants := SexticCMFieldClassInvariants(Dat,Invs);
    return K;
end intrinsic;

intrinsic SexticCMFieldClassNumber(Dat::DBUser,DABC::[RngIntElt])
    -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(DABC,2); require bool : error_string;
    bool, filename := ExistsSexticCMFieldDataFile(DABC);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    h := StringToInteger(Gets(file));
    delete file;
    return h;
end intrinsic;

intrinsic SexticCMFieldClassInvariants(Dat::DBUser,DABC::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(DABC,2); require bool : error_string;
    bool, filename := ExistsSexticCMFieldDataFile(DABC);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file);
    h_invs := StringToIntegerSequence(Gets(file));
    delete file;
    return h_invs;
end intrinsic;

intrinsic SexticCMFieldType(Dat::DBUser,DABC::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(DABC,2); require bool : error_string;
    bool, filename := ExistsSexticCMFieldDataFile(DABC);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file);
    _ := Gets(file);
    t_invs := StringToInteger(Gets(file));
    delete file;
    return IntegerToTypeInvariants(t_invs);
end intrinsic;

intrinsic SexticCMReflexFieldInvariants(Dat::DBUser,DABC::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(DABC,2); require bool : error_string;
    bool, filename := ExistsSexticCMFieldDataFile(DABC);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Sextic CM type
    require t ne 0 :
        "Argument 2 must be invariants of a primitive sextic CM field."; 
    CMinv_r := StringToIntegerSequence(Gets(file));
    delete file;
    return CMinv_r;
end intrinsic;

intrinsic SexticCMHilbertClassField(Dat::DBUser,DABC::[RngIntElt]) -> FldNum
    {}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(DABC,2); require bool : error_string;
    bool, filename := ExistsSexticCMFieldDataFile(DABC);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Sextic CM type
    if true then // t eq 2 then
        _ := Gets(file); // Sextic CM reflex invariants
    end if;
    K := SexticCMField(DABC); 
    s := Gets(file);
    if IsEof(s) then
        delete file;
        SexticCMFieldWrite(K : HCF := true);
        return SexticCMHilbertClassField(Dat,DABC);
    else
        s := StringToInteger(s); 
    end if;
    polys := [];
    for i in [1..s] do
        deg := StringToInteger(Gets(file));
        cffs := [ ];
        for j in [0..deg] do
            // integral coefficient in K:
            c := K!StringToIntegerSequence(Gets(file)); 
            m := StringToInteger(Gets(file)); // denominator of coefficient
            Append(~cffs,c/m);
        end for;
        Append(~polys,Polynomial(cffs));
    end for;
    H := NumberField(polys : Abs, DoLinearExtension);
    delete file;
    return H;
end intrinsic;

intrinsic SexticCMAbsoluteHilbertClassField(Dat::DBUser,DABC::[RngIntElt])
    -> FldNum
    {}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(DABC,2); require bool : error_string;
    bool, filename := ExistsSexticCMFieldDataFile(DABC);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Sextic CM type
    if true then // t eq 2 then
        _ := Gets(file); // Sextic CM reflex invariants
    end if;
    K := SexticCMField(DABC); 
    s := Gets(file);
    if IsEof(s) then
        delete file;
        SexticCMFieldWrite(K : HCF := true);
        return SexticCMAbsoluteHilbertClassField(Dat,DABC);
    else
        s := StringToInteger(s); 
    end if;
    polys := [];
    for i in [1..s] do
        deg := StringToInteger(Gets(file)); // degree of polynomial
        for j in [0..deg] do
            _ := Gets(file); // coefficient in K
            _ := Gets(file); // denominator of coefficient
        end for;
    end for;
    // Absolute defining polynomial for Hilbert class field:
    H := NumberField(Polynomial(StringToIntegerSequence(Gets(file))));
    // Generator for K:
    a := H!StringToIntegerSequence(Gets(file));
    m := StringToInteger(Gets(file));
    if m ne 1 then a /:= m; end if;
    K := NumberField(MinimalPolynomial(a));
    phi := hom< K->H | a >; 
    delete file;
    return H, phi;
end intrinsic;

intrinsic SexticCMHilbertClassFieldIntegralBasis(
    Dat::DBUser,DABC::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, error_string := IsValidDABC(DABC,2); require bool : error_string;
    bool, filename := ExistsSexticCMFieldDataFile(DABC);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    h := StringToInteger(Gets(file)); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Sextic CM type
    if true then // t eq 2 then
        _ := Gets(file); // Sextic CM reflex invariants
    end if;
    K := SexticCMField(DABC); 
    s := Gets(file);
    if IsEof(s) then
        delete file;
        SexticCMFieldWrite(K : HCF := true);
        return SexticCMHilbertClassFieldIntegralBasis(Dat,DABC);
    else
        s := StringToInteger(s); 
    end if;
    polys := [];
    for i in [1..s] do
        deg := StringToInteger(Gets(file)); // degree of polynomial
        for j in [0..deg] do
            _ := Gets(file); // coefficient in K
            _ := Gets(file); // denominator of coefficient
        end for;
    end for;
    // Absolute defining polynomial for Hilbert class field:
    H := NumberField(Polynomial(StringToIntegerSequence(Gets(file))));
    // Generator for K:
    _ := Gets(file);
    _ := Gets(file);
    // Generators for H/K:
    for i in [1..s] do
        _ := Gets(file); // coefficients of generator
        _ := Gets(file); // denominator of coefficients
    end for;
    B := [ H | ];
    for i in [1..4*h] do
        c := StringToIntegerSequence(Gets(file)); // coefficients of basis element
        m := StringToInteger(Gets(file)); // denominator of coefficients
        Append(~B,H!c/m);
    end for;
    delete file;
    return B;
end intrinsic;

intrinsic SexticCMFieldInvariants(Dat::DBUser) -> SeqEnum
    {The list of sextic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Sextic CM fields" :
        "Argument 1 must be the database of sextic CM fields.";
    return &cat[ SexticCMFieldInvariants(Dat,D) : D in SexticCMRealSubfieldDiscriminants(Dat) ];
end intrinsic;    

intrinsic SexticCMFieldInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {The list of sextic CM field invariants [D,A,B,C] represented in the database.}
    require Dat`DBIdentifier eq "Sextic CM fields" :
        "Argument 1 must be the database of sextic CM fields.";
    require D mod 4 in {0,1} and D gt 0 : "Argument 2 must be a real discriminant";
    DABCInvs := [ ];
    D1 := IsSquare(D) select 1 else FundamentalDiscriminant(D);
    bool, D2 := IsSquare(D div D1); assert bool;
    rdisc1_str := pad_int(D1, rdisc1_len);
    rdisc2_str := pad_int(D2, rdisc2_len);
    dirpath1 := DATDIR * rdisc1_str * "/";
    if System("test -d " * dirpath1) ne 0 then
        return DABCInvs;
    end if;
    dirpath2 := dirpath1 * rdisc2_str * "/";
    if System("test -d " * dirpath2) ne 0 then
        return DABCInvs;
    end if;
    FILES := POpen("find " * dirpath2 * " -name fldcm.*.dbz", "r");
    while true do
        file := Gets(FILES);
        if IsEof(file) then break; end if;
        split_string := Split(file,"/");
        dixmier_string := split_string[#split_string];
        _, Astr, Bstr, Cstr := Explode(Split(dixmier_string,".")); 
        A := StringToInteger(Astr);
        B := StringToInteger(Bstr);
        C := StringToInteger(Cstr);
        Append(~DABCInvs,[D,A,B,C]);
    end while;
    return DABCInvs;
end intrinsic;    

intrinsic SexticCMRealSubfieldDiscriminants(Dat::DBUser) -> SeqEnum
    {The list of discriminants D such that some [D,A,B] is reresented
    in the database.}
    require Dat`DBIdentifier eq "Sextic CM fields" :
        "Argument 1 must be the database of sextic CM fields.";
    RMInvs := [ ];
    for i in [0..9] do
        istr := Sprint(i);
        DIRS := POpen("ls -d " * DATDIR * "0" * istr * "*", "r");
        while true do
            dir := Gets(DIRS);
            if IsEof(dir) then break; end if;
            split_string := Split(dir,"/");
            Dstr := split_string[#split_string];
            D := StringToInteger(Dstr);
            Append(~RMInvs,D);
        end while;
    end for;
    return RMInvs;
end intrinsic;    

intrinsic SexticCMFieldInvariantsWithClassNumber(
    Dat::DBUser,h::RngIntElt) -> SeqEnum
    {The sextic CM field invariants with class number h}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    return &cat[ SexticCMFieldInvariantsWithClassNumber(Dat,h,t) : t in [0..6] ];
end intrinsic;

intrinsic SexticCMFieldInvariantsWithClassNumber(
    Dat::DBUser,h::RngIntElt,t::RngIntElt) -> SeqEnum
    {The sextic CM field invariants with class number h and type t,
    where t signifies the Galois group type.}
    require Dat`DBIdentifier eq "Sextic CM fields" : 
        "Argument 1 must be the database of sextic CM fields.";
    bool, filename := ExistsSexticCMClassNumberDataFile(h,t);
    if not bool then return [ ]; end if;
    DABC_List := [ ];
    file := POpen("bunzip2 -c " * filename, "r");
    DABC := Gets(file);
    while not IsEof(DABC) do
        Append(~DABC_List,StringToIntegerSequence(DABC));
        DABC := Gets(file);
    end while;
    return DABC_List;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// File access for sextic CM fields
//////////////////////////////////////////////////////////////////////////////

function SexticCMFieldFilename(D,A,B,C)
    assert D mod 4 in {0,1};
    D1 := IsSquare(D) select 1 else FundamentalDiscriminant(D);
    bool, D2 := IsSquare(D div D1); assert bool;
    rdisc1_str := pad_int(D1, rdisc1_len);
    rdisc2_str := pad_int(D2, rdisc2_len);
    symm1_str := pad_int(A, symm1_len);
    symm2_str := pad_int(B, symm2_len);
    symm3_str := pad_int(C, symm3_len);
    dirpath1 := DATDIR * rdisc1_str * "/";
    dirpath2 := dirpath1 * rdisc2_str * "/";
    filename := &*[ dirpath2, "fldcm.",
        symm1_str, ".", symm2_str, ".", symm3_str, ".db" ];   
    return filename, dirpath1, dirpath2;
end function;

function IsInSexticCMFieldDomain(DABC)
    if Type(DABC) eq FldNum then
        if not IsSexticCMField(DABC) then
            return false, "Argument must be an integer sequence or sextic CM field.";
        end if;
    elif ExtendedType(DABC) ne SeqEnum[RngIntElt] or #DABC ne 4 then 
        return false, "Argument must be an integer sequence or sextic CM field.";
    end if;
    return true, "";
end function;

function ExistsSexticCMFieldDataFile(DABC)
    if Type(DABC) eq FldNum then
        DABC := SexticCMFieldInvariants(DABC);
    end if;
    D,A,B,C := Explode(DABC);
    filename, dirpath1, dirpath2 := SexticCMFieldFilename(D,A,B,C);
    t := System("test -d " * dirpath1);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -d " * dirpath2);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function SexticCMFieldDataFile(D,A,B,C)
    filename, dirpath1, dirpath2 := SexticCMFieldFilename(D,A,B,C);
    if System("test -d " * dirpath1) ne 0 then
        System("mkdir " * dirpath1);
        System("chmod a+rx " * dirpath1);
    end if;
    if System("test -d " * dirpath2) ne 0 then
        System("mkdir " * dirpath2);
        System("chmod a+rx " * dirpath2);
    end if;
    System("touch " * filename);
    System("chmod a+r " * filename);
    return filename;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

procedure SexticCMFieldWrite(K : HCF := false)
    D, A, B, C := Explode(SexticCMFieldInvariants(K));
    filename := SexticCMFieldDataFile(D,A,B,C);
    h_invs := CMFieldClassInvariants(K);
    if #h_invs eq 0 then h_invs := [1]; end if; 
    h := &*h_invs;
    file := Open(filename,"w"); Flush(file);
    /*
    FIRST BLOCK (elementary invariants)
      h: class number
      n1 n2 ... nt : abelian invariants of class group
      D a b c d : reflex field invariants (if non-normal extension)
    */
    Puts(file,Sprint(h));
    Puts(file,&*[ Sprint(c) * " " : c in h_invs ]);
    t_invs := SexticCMFieldType(K);
    t := TypeInvariantsToInteger(t_invs);
    Puts(file,Sprint(t));
    ReflexFlds := SexticCMReflexFields(K);
    for K_r in ReflexFlds do
        CMinv_r := CMFieldInvariants(K_r);
        Puts(file,&*[ Sprint(X) * " " : X in CMinv_r ]);
    end for;
    /*
    SECOND BLOCK (Hilbert class field)
      s: number of generators for Hilbert class field
      f_1,...,f_s: defining polynomials as relative extension of K
      for i in (1..s):
         for j in (0..deg(f_i)):
           a_ij/m_ij
      f: absolute defining polynomial for H
      a: image of generator of K (in terms of absolute extension)
      a_1,...,a_s: images of generators for H/K (in absolute extension)
      B: basis for O_H (in terms of absolute polynomial)
    N.B. Each element x/m of H is stored as (x in ZZ[a],m) on two lines.
    */
    if HCF then
        if h eq 1 then
            polys := [ Polynomial([K|-1,1]) ]; 
            H1 := NumberField(polys[1] : DoLinearExtension); 
        else
            H1 := HilbertClassField(K);
            polys := DefiningPolynomial(H1);
            if Type(polys) eq RngUPolElt then
                polys := [ polys ];
            end if;
        end if;
        // Induce the maximal order computation in this model,
        // which will be needed for OptimizedRepresentation 
        // and later determination of the maximal order of the 
        // absolute field.
        _ := MaximalOrder(H1);
        H2 := OptimizedRepresentation(AbsoluteField(H1));
        s := Ngens(H1); 
        Puts(file,Sprint(s));
        for i in [1..s] do
            cffs := Eltseq(polys[i]);
            Puts(file,Sprint(#cffs-1)); // degree of polynomial
            for a in cffs do
                cffa := Eltseq(a); 
                den := LCM([ Denominator(r) : r in cffa ]);
                Puts(file,&*[ Sprint(r*den) * " " : r in cffa ]);
                Puts(file,Sprint(den));
            end for;
        end for;
        // Absolute defining polynomial for Hilbert class field:
        f := DefiningPolynomial(H2);
        cffs := Eltseq(f);
        den := LCM([ Denominator(r) : r in cffs ]);
        Puts(file,&*[ Sprint(r*den) * " " : r in cffs ]);
        // Generator for K:
        cffa := Eltseq(H2!K.1); 
        den := LCM([ Denominator(r) : r in cffa ]);
        Puts(file,&*[ Sprint(r*den) * " " : r in cffa ]);
        Puts(file,Sprint(den));
        // Generators for H/K:
        for i in [1..s] do
            cffa := Eltseq(H2!H1.i); 
            den := LCM([ Denominator(r) : r in cffa ]);
            Puts(file,&*[ Sprint(r*den) * " " : r in cffa ]);
            Puts(file,Sprint(den));
        end for;
        // Generators for O_H:
        B := [ H2!x : x in Basis(MaximalOrder(H2)) ];
        for a in B do
            cffa := Eltseq(a);
            den := LCM([ Denominator(r) : r in cffa ]);
            Puts(file,&*[ Sprint(r*den) * " " : r in cffa ]);
            Puts(file,Sprint(den));
        end for;
    end if; 
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
    for K_r in ReflexFlds do
        if Degree(K_r) eq 8 and not CMinv_r in OcticCMFieldDatabase() then
            OcticCMFieldWrite(K_r);
        end if;
    end for;
end procedure;

//////////////////////////////////////////////////////////////////////////////
// File access for sextic CM class numbers 
//////////////////////////////////////////////////////////////////////////////

function SexticCMClassNumberFilename(h,t)
    class_str := pad_int(h, class_len);
    type_str := Sprint(t);
    dirpath := DATDIR * "Class/";
    filename := &*[ dirpath, "class.", class_str, ".", type_str, ".db" ];   
    return filename, dirpath;
end function;

function ExistsSexticCMClassNumberDataFile(h,t)
    filename, dirpath := SexticCMClassNumberFilename(h,t);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function SexticCMClassNumberDataFile(h,t)
    filename, dirpath := SexticCMClassNumberFilename(h,t);
    if System("test -d " * dirpath) ne 0 then
        System("mkdir " * dirpath);
    end if;
    System("touch " * filename);
    return filename;
end function;

/*
Currently storing class invariants so need to modify...

procedure SexticCMClassNumberWrite(DABC,h)
    D, A, B, C := Explode(DABC);
    DBCM := SexticCMFieldDatabase();
    DABC_classes := SexticCMFieldInvariantsWithClassNumber(DBCM,h);
    if DABC in DABC_classes then return; end if;
    Append(~DABC_classes,DABC);
    filename := SexticCMClassNumberDataFile(D,h);
    file := Open(filename,"w"); Flush(file);
    for DABC_i in DABC_classes do
        Puts(file,&+[ Sprint(S) * " " : S in DABC_i ]);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;
*/
