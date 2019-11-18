//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                           OCTIC CM FIELDS                                //
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

DATDIR := GetEchidnaDatabaseRoot() * "/FldCM/8/";
rdisc_len := 12;
rdisc1_len := 6;
rdisc2_len := 6;
symm1_len := 8;
symm2_len := 8;
symm3_len := 8;
symm4_len := 8;
class_len := 6;

//////////////////////////////////////////////////////////////////////////////

import "sextic_cm_fields.m" : SexticCMFieldWrite;

//////////////////////////////////////////////////////////////////////////////

forward OcticCMFieldDataFile, OcticCMFieldWrite;
forward IsInOcticCMFieldDomain, ExistsOcticCMFieldDataFile;
forward OcticCMClassNumberDataFile, ExistsOcticCMClassNumberDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic OcticCMFieldDatabase() -> DBUser
    {The database of octic CM fields.}
    Dat := New(DBUser);
    Dat`Invariant := 8;
    Dat`DBIdentifier := "Octic CM fields";
    Dat`WriteFunction := OcticCMFieldWrite;
    Dat`ExistsFunction := ExistsOcticCMFieldDataFile;
    Dat`IsInDomainFunction := IsInOcticCMFieldDomain;
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
//////////////////////////////////////////////////////////////////////////////

function IsValidInvs(Invs,i)
    if #Invs ne 5 then
        return false,
            Sprintf("Argument %o must be a sequence of five integers.",i);
    end if;
    D, a, b, c, d := Explode(Invs);
    bool := D mod 4 in {0,1} and D gt 1;
    error_string :=
        Sprintf("Argument %o, element 1, must be a positive discriminant.",i);
    if not bool then
        return bool, error_string;
    end if;
    for j in [2,3,4] do
        bool := Invs[j] ge 0;
        if not bool then
            error_string := Sprintf("Argument %o, element %o, must be non-negative.",j,i);
            return bool, error_string;
        end if;
    end for;
    D1 := -27*a^4*d^2 + 18*a^3*b*c*d - 4*a^3*c^3 - 4*a^2*b^3*d + a^2*b^2*c^2
        + 144*a^2*b*d^2 - 6*a^2*c^2*d - 80*a*b^2*c*d + 18*a*b*c^3 - 192*a*c*d^2
        + 16*b^4*d - 4*b^3*c^2 - 128*b^2*d^2 + 144*b*c^2*d - 27*c^4 + 256*d^3;
    bool := D1 mod D eq 0 and IsSquare(D1 div D);
    error_string := Sprintf("Argument %o is not valid.",i);
    if not bool then
        return bool, error_string;
    end if;
    return true, "";
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

function IntegerToTypeInvariants(t_invs)
    case t_invs:
    when 0:
        return [4,2];
    when 1:
        return [8,2];
    when 2:
        return [12,2];
    when 3:
        return [12,4];
    when 4:
        return [12,8];
    when 5:
        return [12,16];
    when 6:
        return [24,2];
    when 7:
        return [24,2];
    when 8:
        return [24,4];
    when 9:
        return [24,8];
    when 10:
        return [24,16];
    end case;
    error if true, "Invalid integer for type specification.";
end function;

function TypeInvariantsToInteger(t_invs)
    case t_invs:
    when [4,2]:
        return 0;
    when [8,2]:
        return 1;
    when [12,2]:
        return 2;
    when [12,4]:
        return 3;
    when [12,8]:
        return 4;
    when [12,16]:
        return 5;
    when [24,2]:
        return 6;
    when [24,2]:
        return 7;
    when [24,4]:
        return 8;
    when [24,8]:
        return 9;
    when [24,16]:
        return 10;
    end case;
    error if true, "Invalid type specification.";
end function;

//////////////////////////////////////////////////////////////////////////////
// Access functions
//////////////////////////////////////////////////////////////////////////////

intrinsic OcticCMField(Dat::DBUser,Invs::[RngIntElt]) -> SeqEnum
    {Given an integer sequence Invs = [D,a,b,c,d] return the octic CM field
    with defining polynomial x^8 + a*x^6 + b*x^4 + c*x^2 + d. The following
    fields are automatically assigned:
    
    K`IsCMField,
    K`OcticCMFieldInvariants,
    K`OcticCMFieldType,
    K`TotallyRealSubfield,
    K`CMFieldClassInvariants.

    Note that D must be the discriminant of the defining polynomial x^4 + a*x^3
    + b*x^2 + c*x + d for the totaly real subfield.}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    require Invs in Dat : "Argument 2 is not in database argument 1.";
    D, a, b, c, d := Explode(Invs);
    K := NumberField(Polynomial([d,0,c,0,b,0,a,0,1]));
    K`IsCMField := true;
    K`OcticCMFieldInvariants := Invs;
    K`OcticCMFieldType := OcticCMFieldType(Dat,Invs);
    K`TotallyRealSubfield := sub< K | K.1^2 >;
    K`CMFieldClassInvariants := OcticCMFieldClassInvariants(Dat,Invs);
    return K;
end intrinsic;

intrinsic OcticCMFieldClassNumber(Dat::DBUser,Invs::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    bool, filename := ExistsOcticCMFieldDataFile(Invs);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    h := StringToInteger(Gets(file));
    delete file;
    return h;
end intrinsic;

intrinsic OcticCMFieldClassInvariants(Dat::DBUser,Invs::[RngIntElt])
    -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    bool, filename := ExistsOcticCMFieldDataFile(Invs);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file);
    h_invs := StringToIntegerSequence(Gets(file));
    delete file;
    return h_invs;
end intrinsic;

intrinsic OcticCMFieldType(Dat::DBUser,Invs::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    bool, filename := ExistsOcticCMFieldDataFile(Invs);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file);
    _ := Gets(file);
    t := StringToInteger(Gets(file));
    delete file;
    return IntegerToTypeInvariants(t);
end intrinsic;

intrinsic OcticCMReflexFieldInvariants(
    Dat::DBUser,Invs::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    bool, filename := ExistsOcticCMFieldDataFile(Invs);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Octic CM type
    require t in {2,3} :
        "Argument 2 must be invariants of a primitive octic CM field with sextic reflex."; 
    Invs_r := StringToIntegerSequence(Gets(file));
    delete file;
    return Invs_r;
end intrinsic;

intrinsic OcticCMHilbertClassField(Dat::DBUser,Invs::[RngIntElt]) -> FldNum
    {}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    bool, filename := ExistsOcticCMFieldDataFile(Invs);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Octic CM type
    if t eq 2 then
        _ := Gets(file); // Octic CM reflex invariants
    end if;
    K := OcticCMField(Invs); 
    s := Gets(file);
    if IsEof(s) then
        delete file;
        OcticCMFieldWrite(K : HCF := true);
        return OcticCMHilbertClassField(Dat,Invs);
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

intrinsic OcticCMAbsoluteHilbertClassField(Dat::DBUser,Invs::[RngIntElt])
    -> FldNum
    {}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    bool, filename := ExistsOcticCMFieldDataFile(Invs);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Octic CM type
    if t eq 2 then
        _ := Gets(file); // Octic CM reflex invariants
    end if;
    K := OcticCMField(Invs); 
    s := Gets(file);
    if IsEof(s) then
        delete file;
        OcticCMFieldWrite(K : HCF := true);
        return OcticCMAbsoluteHilbertClassField(Dat,Invs);
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

intrinsic OcticCMHilbertClassFieldIntegralBasis(
    Dat::DBUser,Invs::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, error_string := IsValidInvs(Invs,2); require bool : error_string;
    bool, filename := ExistsOcticCMFieldDataFile(Invs);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename, "r");
    h := StringToInteger(Gets(file)); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Octic CM type
    if t eq 2 then
        _ := Gets(file); // Octic CM reflex invariants
    end if;
    K := OcticCMField(Invs); 
    s := Gets(file);
    if IsEof(s) then
        delete file;
        OcticCMFieldWrite(K : HCF := true);
        return OcticCMHilbertClassFieldIntegralBasis(Dat,Invs);
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

intrinsic OcticCMFieldInvariants(Dat::DBUser) -> SeqEnum
    {The list of octic CM field invariants represented in the database.}
    require Dat`DBIdentifier eq "Octic CM fields" :
        "Argument 1 must be the database of octic CM fields.";
    return &cat[ OcticCMFieldInvariants(Dat,D) : D in OcticCMRealSubfieldDiscriminants(Dat) ];
end intrinsic;    

intrinsic OcticCMFieldInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {The list of octic CM field invariants represented in the database.}
    require Dat`DBIdentifier eq "Octic CM fields" :
        "Argument 1 must be the database of octic CM fields.";
    CMInvs := [ ];
    if IsSquare(D) then
        D1 := 1;
    else
        D1 := FundamentalDiscriminant(D);
    end if;
    bool, D2 := IsSquare(D div D1); assert bool;
    rdisc1_str := pad_int(D1, rdisc1_len);
    rdisc2_str := pad_int(D2, rdisc2_len);
    dirpath1 := DATDIR * rdisc1_str * "/";
    if System("test -d " * dirpath1) ne 0 then
        return CMInvs;
    end if;
    dirpath2 := dirpath1 * rdisc2_str * "/";
    if System("test -d " * dirpath2) ne 0 then
        return CMInvs;
    end if;
    FILES := POpen("find " * dirpath2 * " -name fldcm.*.dbz", "r");
    while true do
        file := Gets(FILES);
        if IsEof(file) then break; end if;
        split_string := Split(file,"/");
        fldcm_string := split_string[#split_string];
        _, astr, bstr, cstr, dstr := Explode(Split(fldcm_string,".")); 
        a := StringToInteger(astr);
        b := StringToInteger(bstr);
        c := StringToInteger(cstr);
        d := StringToInteger(dstr);
        Append(~CMInvs,[D,a,b,c,d]);
    end while;
    return CMInvs;
end intrinsic;    

intrinsic OcticCMRealSubfieldDiscriminants(Dat::DBUser) -> SeqEnum
    {The list of discriminants D such that some invariants of discriminants D
    is reresented in the database.}
    require Dat`DBIdentifier eq "Octic CM fields" :
        "Argument 1 must be the database of octic CM fields.";
    RMInvs := [ ];
    for i in [0..9] do
        istr := Sprint(i);
        DIRS := POpen("ls -d " * DATDIR * "/0" * istr * "*", "r");
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

intrinsic OcticCMFieldInvariantsWithClassNumber(
    Dat::DBUser,h::RngIntElt) -> SeqEnum
    {The octic CM field invariants with class number h}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    return &cat[ OcticCMFieldInvariantsWithClassNumber(Dat,h,t) : t in [0..10] ];
end intrinsic;

intrinsic OcticCMFieldInvariantsWithClassNumber(
    Dat::DBUser,h::RngIntElt,t::RngIntElt) -> SeqEnum
    {The octic CM field invariants with class number h and type t,
    where t = 2 signifies an extension of a totally real A_4 field,
    and t = 6 implies an extension of a totally real S_4 field.}
    require Dat`DBIdentifier eq "Octic CM fields" : 
        "Argument 1 must be the database of octic CM fields.";
    bool, filename := ExistsOcticCMClassNumberDataFile(h,t);
    if not bool then return [ ]; end if;
    Invs_List := [ ];
    file := POpen("bunzip2 -c " * filename, "r");
    Invs := Gets(file);
    while not IsEof(Invs) do
        Append(~Invs_List,StringToIntegerSequence(Invs));
        Invs := Gets(file);
    end while;
    return Invs_List;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
// File access for octic CM fields
//////////////////////////////////////////////////////////////////////////////

function OcticCMFieldFilename(D,a,b,c,d)
    assert D mod 4 in {0,1};
    D1 := IsSquare(D) select 1 else FundamentalDiscriminant(D);
    bool, D2 := IsSquare(D div D1); assert bool;
    rdisc1_str := pad_int(D1, rdisc1_len);
    rdisc2_str := pad_int(D2, rdisc2_len);
    symm1_str := pad_int(a, symm1_len);
    symm2_str := pad_int(b, symm2_len);
    symm3_str := pad_int(c, symm3_len);
    symm4_str := pad_int(d, symm4_len);
    dirpath1 := DATDIR * rdisc1_str * "/";
    dirpath2 := dirpath1 * rdisc2_str * "/";
    filename := &*[ dirpath2, "fldcm.",
        symm1_str, ".", symm2_str, ".", symm3_str, ".", symm4_str, ".db" ];   
    return filename, dirpath1, dirpath2;
end function;

function IsInOcticCMFieldDomain(Invs)
    if Type(Invs) eq FldNum then
        if not IsOcticCMField(Invs) then
            return false, "Argument must be an integer sequence or octic CM field.";
        end if;
    elif ExtendedType(Invs) ne SeqEnum[RngIntElt] or #Invs ne 5 then 
        return false, "Argument must be an integer sequence or octic CM field.";
    end if;
    return true, "";
end function;

function ExistsOcticCMFieldDataFile(Invs)
    if Type(Invs) eq FldNum then
        Invs := OcticCMFieldInvariants(Invs);
    end if;
    D,a,b,c,d := Explode(Invs);
    filename, dirpath1, dirpath2 := OcticCMFieldFilename(D,a,b,c,d);
    t := System("test -d " * dirpath1);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -d " * dirpath2);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function OcticCMFieldDataFile(D,a,b,c,d)
    filename, dirpath1, dirpath2 := OcticCMFieldFilename(D,a,b,c,d);
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

procedure OcticCMFieldWrite(K : HCF := false)
    D, a, b, c, d := Explode(OcticCMFieldInvariants(K));
    filename := OcticCMFieldDataFile(D,a,b,c,d);
    h_invs := CMFieldClassInvariants(K);
    if #h_invs eq 0 then h_invs := [1]; end if; 
    h := &*h_invs;
    file := Open(filename,"w"); Flush(file);
    /*
    FIRST BLOCK (elementary invariants)
      h: class number
      n1 n2 ... nt : abelian invariants of class group
      D a b c ... : reflex field invariants (if non-normal extension)
    */
    Puts(file,Sprint(h));
    Puts(file,&*[ Sprint(c) * " " : c in h_invs ]);
    t_invs := OcticCMFieldType(K);
    t := TypeInvariantsToInteger(t_invs);
    Puts(file,Sprint(t));
    ReflexFlds := OcticCMReflexFields(K);
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
        if Degree(K_r) eq 6 and not K_r in SexticCMFieldDatabase() then
            SexticCMFieldWrite(K_r);
        elif Degree(K_r) eq 8 and not K_r in OcticCMFieldDatabase() then
            OcticCMFieldWrite(K_r);
        end if;
    end for;
end procedure;

//////////////////////////////////////////////////////////////////////////////
// File access for octic CM class numbers 
//////////////////////////////////////////////////////////////////////////////

function OcticCMClassNumberFilename(h,t)
    class_str := pad_int(h, class_len);
    type_str := Sprint(t);
    dirpath := DATDIR * "Class/";
    filename := &*[ dirpath, "class.", class_str, ".", type_str, ".db" ];   
    return filename, dirpath;
end function;

function ExistsOcticCMClassNumberDataFile(h,t)
    filename, dirpath := OcticCMClassNumberFilename(h,t);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function OcticCMClassNumberDataFile(h,t)
    filename, dirpath := OcticCMClassNumberFilename(h,t);
    if System("test -d " * dirpath) ne 0 then
        System("mkdir " * dirpath);
    end if;
    System("touch " * filename);
    return filename;
end function;

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////

procedure OcticCMClassNumberWrite(Invs,h)
    D, a, b, c, d := Explode(Invs);
    DBCM := OcticCMFieldDatabase();
    Invs_classes := OcticCMFieldInvariantsWithClassNumber(DBCM,h);
    if Invs in Invs_classes then return; end if;
    Append(~Invs_classes,Invs);
    filename := OcticCMClassNumberDataFile(D,h);
    file := Open(filename,"w"); Flush(file);
    for Invs_i in Invs_classes do
        Puts(file,&+[ Sprint(S) * " " : S in Invs_i ]);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////

