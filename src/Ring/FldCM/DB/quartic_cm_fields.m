//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                      QUARTIC CM FIELD DATABASE                           //
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

DATDIR := GetEchidnaDatabaseRoot() * "/FldCM/4/";
rdisc_len := 10;
trace_len := 6;
snorm_len := 8;
class_len := 6;

//////////////////////////////////////////////////////////////////////////////

forward QuarticCMFieldDataFile, QuarticCMFieldWrite;
forward IsInQuarticCMFieldDomain, ExistsQuarticCMFieldDataFile;
forward QuarticCMClassNumberDataFile, ExistsQuarticCMClassNumberDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic QuarticCMFieldDatabase() -> DBUser
    {The database of quartic CM fields.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Quartic CM fields";
    Dat`Invariant := 4;
    Dat`WriteFunction := QuarticCMFieldWrite;
    Dat`ExistsFunction := ExistsQuarticCMFieldDataFile;
    Dat`IsInDomainFunction := IsInQuarticCMFieldDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                            WRITE FUNCTION                                //
//////////////////////////////////////////////////////////////////////////////

/*
intrinsic Write(Dat::DBUser,K::FldNum,H::FldNum)
    {Write the quartic CM field K with Hilbert class field H to database.}
    require Dat`DBIdentifier eq "Quartic CM fields" :
        "Argument 1 must be the database of quartic CM fields.";
    require IsQuarticCMField(K) and IsSubfield(K,H) :
        "Argument 2 must be a quartic CM field " *
        "and argument 3 its Hilbert class field.";
    val, errstr := QuarticCMFieldWrite(K : HCF := true);
    require val : errstr;
    return;
end intrinsic;
*/

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

function IsValidDAB(DAB,i)
    if #DAB ne 3 then
        return false,
            Sprintf("Argument %o must be a sequence of three integers.",i);
    end if;
    D, A, B := Explode(DAB);
    bool := D mod 4 in {0,1} and D gt 1 and
        not IsSquare(D) and IsFundamental(D);
    error_string :=
        Sprintf("Argument %o, element 1, must be a positive fundamental discriminant.",i);
    if not bool then
        return bool, error_string;
    end if;
    D1 := A^2 - 4*B;
    if not A eq 0 and B lt 0 then
        bool := D1 mod D eq 0 and IsSquare(D1 div D);
        error_string := Sprintf("Argument %o, elements 2 and 3, are not valid.",i);
        if not bool then
            return bool, error_string;
        end if;
    end if;
    return true, "";
end function;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic QuarticCMField(Dat::DBUser,DAB::[RngIntElt]) -> SeqEnum
    {Given an integer sequence [D,A,B] such that A^2 - 4*B = m^2*D, return
    the quartic CM field with defining polynomial X^4 + A*X^2 + B. The
    following fields are automatically assigned:
    
    K`IsCMField,
    K`QuarticCMFieldInvariants,
    K`QuarticCMFieldType,
    K`TotallyRealSubfield,
    K`CMFieldClassInvariants.

    Note that D is the discriminant of the totaly real subfield.}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    require DAB in Dat : "Argument 2 is not in database argument 1.";
    D, A, B := Explode(DAB);
    K := NumberField(Polynomial([B,0,A,0,1]));
    K`IsCMField := true;
    K`QuarticCMFieldInvariants := DAB;
    K`QuarticCMFieldType := QuarticCMFieldType(Dat,DAB);
    K`TotallyRealSubfield := sub< K | K.1^2 >;
    K`CMFieldClassInvariants := QuarticCMFieldClassInvariants(Dat,DAB);
    return K;
end intrinsic;

intrinsic QuarticCMFieldClassNumber(Dat::DBUser,DAB::[RngIntElt])
    -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    bool, filename := ExistsQuarticCMFieldDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    h := StringToInteger(Gets(file));
    delete file;
    return h;
end intrinsic;

intrinsic QuarticCMFieldClassInvariants(Dat::DBUser,DAB::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    D, A, B := Explode(DAB);
    bool, filename := ExistsQuarticCMFieldDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    _ := Gets(file);
    h_invs := StringToIntegerSequence(Gets(file));
    delete file;
    return h_invs;
end intrinsic;

intrinsic QuarticCMFieldType(Dat::DBUser,DAB::[RngIntElt])
    -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    bool, filename := ExistsQuarticCMFieldDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    try
        _ := Gets(file);
        _ := Gets(file);
        t := StringToInteger(Gets(file));
    catch err
        error "Failed to access CM field type for " * Sprint(DAB) * " in file " * filename;
    end try;
    delete file;
    case t:
    when 0:
        return [2,2];
    when 1:
        return [4];
    when 2:
        return [8];
    end case;
    require false : "Database entry has invalid type specification.";
end intrinsic;

intrinsic QuarticCMReflexFieldInvariants(Dat::DBUser,DAB::[RngIntElt]) -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    bool, filename := ExistsQuarticCMFieldDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Quartic CM type
    if t eq 1 then
        return DAB;
    end if;
    require t ne 0 :
        "Argument 2 must be invariants of a cyclic or non-normal quartic CM field."; 
    DAB_r := StringToIntegerSequence(Gets(file));
    delete file;
    return DAB_r;
end intrinsic;

intrinsic QuarticCMHilbertClassField(Dat::DBUser,DAB::[RngIntElt]) -> FldNum
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    bool, filename := ExistsQuarticCMFieldDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Quartic CM type
    if t eq 0 then
        //_ := Gets(file); // Quartic CM reflex invariants
        //_ := Gets(file); // Quartic CM reflex invariants
    elif t eq 1 then
        //_ := Gets(file); // Quartic CM reflex invariants
    elif t eq 2 then
        _ := Gets(file); // Quartic CM reflex invariants
    end if;
    K := QuarticCMField(Dat,DAB); 
    s := Gets(file);
    if IsEof(s) or #StringToIntegerSequence(s) gt 1 then
        delete file;
        QuarticCMFieldWrite(K : HCF := true);
        return QuarticCMHilbertClassField(Dat,DAB);
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

intrinsic QuarticCMAbsoluteHilbertClassField(Dat::DBUser,DAB::[RngIntElt])
    -> FldNum
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    bool, filename := ExistsQuarticCMFieldDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    _ := Gets(file); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Quartic CM type
    if t eq 0 then
        //_ := Gets(file); // Quartic CM reflex invariants
        //_ := Gets(file); // Quartic CM reflex invariants
    elif t eq 1 then
        //_ := Gets(file); // Quartic CM reflex invariants
    elif t eq 2 then
        _ := Gets(file); // Quartic CM reflex invariants
    end if;
    K := QuarticCMField(DAB); 
    s := Gets(file);
    if IsEof(s) or #StringToIntegerSequence(s) gt 1 then
        delete file;
        QuarticCMFieldWrite(K : HCF := true);
        return QuarticCMAbsoluteHilbertClassField(Dat,DAB);
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

intrinsic QuarticCMHilbertClassFieldIntegralBasis(Dat::DBUser,DAB::[RngIntElt])
    -> SeqEnum
    {}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, error_string := IsValidDAB(DAB,2); require bool : error_string;
    bool, filename := ExistsQuarticCMFieldDataFile(DAB);
    require bool : "Argument 1 contains no data file for this number field.";
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    h := StringToInteger(Gets(file)); // Class number
    _ := Gets(file); // Class group abelian invariants
    t := StringToInteger(Gets(file)); // Quartic CM type
    if t eq 0 then
        //_ := Gets(file); // Quartic CM reflex invariants
        //_ := Gets(file); // Quartic CM reflex invariants
    elif t eq 1 then
        //_ := Gets(file); // Quartic CM reflex invariants
    elif t eq 2 then
        _ := Gets(file); // Quartic CM reflex invariants
    end if;
    K := QuarticCMField(DAB); 
    s := Gets(file);
    if IsEof(s) or #StringToIntegerSequence(s) gt 1 then
        delete file;
        QuarticCMFieldWrite(K : HCF := true);
        return QuarticCMHilbertClassFieldIntegralBasis(Dat,DAB);
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

intrinsic QuarticCMFieldInvariants(Dat::DBUser) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    require Dat`DBIdentifier eq "Quartic CM fields" :
        "Argument 1 must be the database of quartic CM fields.";
    return &cat[ QuarticCMFieldInvariants(Dat,D) : D in QuarticCMRealSubfieldDiscriminants(Dat) ];
end intrinsic;    

intrinsic QuarticCMFieldInvariants(Dat::DBUser,D::RngIntElt) -> SeqEnum
    {The list of quartic CM field invariants [D,A,B] represented in the database.}
    DABInvs := [ ];
    rdisc_str := pad_int(D, rdisc_len);
    case Dat`DBIdentifier:
    when "Quartic CM fields":
        dirpath := DATDIR * rdisc_str * "/";
    when "Igusa LIX":
        DATDIR_LIX := GetEchidnaDatabaseRoot() * "/IgusaLIX/";
        dirpath := DATDIR_LIX * rdisc_str * "/";
    else
        require false :
            "Argument 1 must be the database of quartic CM fields or Igusa LIX invariants.";
    end case;
    if System("test -d " * dirpath) ne 0 then
        return DABInvs;
    end if;
    case Dat`DBIdentifier:
    when "Quartic CM fields":
        FILES := POpen("find " * dirpath * " -name fldcm.*.dbz", "r");
    when "Igusa LIX":
        FILES := POpen("find " * dirpath * " -name igusa.*.dbz", "r");
    end case;
    while true do
        file := Gets(FILES);
        if IsEof(file) then break; end if;
        split_string := Split(file,"/");
        igusa_string := split_string[#split_string];
        _, Astr, Bstr := Explode(Split(igusa_string,".")); 
        A := StringToInteger(Astr);
        B := StringToInteger(Bstr);
        Append(~DABInvs,[D,A,B]);
    end while;
    return DABInvs;
end intrinsic;    

intrinsic QuarticCMRealSubfieldDiscriminants(Dat::DBUser) -> SeqEnum
    {The list of discriminants D such that some [D,A,B] is reresented in the database.}
    require Dat`DBIdentifier eq "Quartic CM fields" :
        "Argument 1 must be the database of quartic CM fields.";
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

intrinsic QuarticCMFieldInvariantsWithClassNumber(
    Dat::DBUser,h::RngIntElt) -> SeqEnum
    {The quartic CM field invariants with class number h.}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    return &cat[ QuarticCMFieldInvariantsWithClassNumber(Dat,h,t) : t in [0,1,2] ];
end intrinsic;

intrinsic QuarticCMFieldInvariantsWithClassNumber(
    Dat::DBUser,h::RngIntElt,t::RngIntElt) -> SeqEnum
    {The quartic CM field invariants with class number h and type t,
    where t = 0 signifies biquadratic, t = 1 signifies cyclic, and
    t = 2 corresponds to nonnormal fields.}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    bool, filename := ExistsQuarticCMClassNumberDataFile(h,t);
    if not bool then return [ ]; end if;
    DAB_List := [ ];
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    DAB := Gets(file);
    while not IsEof(DAB) do
        Append(~DAB_List,StringToIntegerSequence(DAB)[[1..3]]);
        DAB := Gets(file);
    end while;
    return DAB_List;
end intrinsic;

intrinsic QuarticCMFieldInvariantsWithClassInvariants(
    Dat::DBUser,h_invs::[RngIntElt],t::RngIntElt) -> SeqEnum
    {The quartic CM field invariants with class invariants h_invs and type t,
    where t = 0 signifies biquadratic, t = 1 signifies cyclic, and
    t = 2 corresponds to nonnormal fields.}
    require Dat`DBIdentifier eq "Quartic CM fields" : 
        "Argument 1 must be the database of quartic CM fields.";
    n := #h_invs;
    if n eq 0 or h_invs[1] le 0 then
        require false : "Argument 2 must be a valid sequence of abelian invariants.";
    end if;
    for i in [1..n-1] do
        if h_invs[i+1] mod h_invs[i] ne 0 then
            require false : "Argument 2 must be a valid sequence of abelian invariants.";
        end if;
    end for;
    h := &*h_invs;
    bool, filename := ExistsQuarticCMClassNumberDataFile(h,t);
    if not bool then return [ ]; end if;
    file := POpen("bunzip2 -c " * filename * " 2>/dev/null", "r");
    DAB_List := [ ];
    DAB_Line := Gets(file);
    while not IsEof(DAB_Line) do
        DAB_seq := StringToIntegerSequence(DAB_Line);
        DAB1 := DAB_seq[[1..3]]; 
        if t ne 2 then
            h_invs1 := DAB_seq[[4..#DAB_seq]];
        else
            h_invs1 := DAB_seq[[7..#DAB_seq]];
        end if;
        if h_invs1 eq h_invs then 
            Append(~DAB_List,DAB1);
        end if;
        DAB_Line := Gets(file);
    end while;
    return DAB_List;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                      QUARTIC FIELD WRITE ACCESS                          //
//////////////////////////////////////////////////////////////////////////////

procedure QuarticCMFieldWrite(K : HCF := false)
    D, A, B := Explode(QuarticCMFieldInvariants(K));
    assert B ne 0; // Check consistency...
    filename := QuarticCMFieldDataFile(D,A,B);
    h_invs := CMFieldClassInvariants(K);
    if #h_invs eq 0 then h_invs := [1]; end if; 
    h := &*h_invs;
    file := Open(filename,"w"); Flush(file);
    /*
    FIRST BLOCK (elementary invariants)
      h: class number
      n1 n2 ... nt : abelian invariants of class group
      D A B : reflex field invariants (if non-normal extension)
    */
    Puts(file,Sprint(h));
    Puts(file,&*[ Sprint(c) * " " : c in h_invs ]);
    t_invs := QuarticCMFieldType(K);
    case t_invs:
    when [2,2]:
        t := 0;
    when [4]:
        t := 1;
    when [8]:
        t := 2;
    end case;
    Puts(file,Sprint(t));
    if t eq 0 then
        // skip
        // skip
    elif t eq 1 then
        // skip
    elif t eq 2 then
        K_r := QuarticCMReflexField(K);
        DAB_r := QuarticCMFieldInvariants(K_r);
        Puts(file,&*[ Sprint(X) * " " : X in DAB_r ]);
    end if;
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
    if t eq 2 then
        // Write the reflex field to database:
        DBCM := QuarticCMFieldDatabase();
        if not DAB_r in DBCM then
            QuarticCMFieldWrite(K_r);
        end if;
    end if;
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function QuarticCMFieldFilename(D,A,B)
    rdisc_str := pad_int(D, rdisc_len);
    trace_str := pad_int(A, trace_len);
    snorm_str := pad_int(B, snorm_len);
    dirpath := DATDIR * rdisc_str * "/";
    filename := &*[ dirpath, "fldcm.", trace_str, ".", snorm_str, ".db" ];   
    return filename, dirpath;
end function;

function IsInQuarticCMFieldDomain(DAB)
    if Type(DAB) eq FldNum then
        if not IsQuarticCMField(DAB) then
            return false, "Argument must be an integer sequence or quartic CM field.";
        end if;
    elif ExtendedType(DAB) ne SeqEnum[RngIntElt] or #DAB ne 3 then 
        return false, "Argument must be an integer sequence or quartic CM field.";
    end if;
    return true, "";
end function;

function ExistsQuarticCMFieldDataFile(X)
    if Type(X) eq FldNum then
        X := QuarticCMFieldInvariants(X);
    end if;
    D,A,B := Explode(X);
    filename, dirpath := QuarticCMFieldFilename(D,A,B);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function QuarticCMFieldDataFile(D,A,B)
    filename, dirpath := QuarticCMFieldFilename(D,A,B);
    if System("test -d " * dirpath) ne 0 then
        System("mkdir " * dirpath);
        System("chmod a+rx " * dirpath);
    end if;
    System("touch " * filename);
    System("chmod a+r " * filename);
    return filename;
end function;

//////////////////////////////////////////////////////////////////////////////
//                   FILE STRUCTURE FOR CLASS NUMBERS                       //
//////////////////////////////////////////////////////////////////////////////

function QuarticCMClassNumberFilename(h,t)
    class_str := pad_int(h, class_len);
    type_str := Sprint(t);
    dirpath := DATDIR * "Class/";
    filename := &*[ dirpath, "class.", class_str, ".", type_str, ".db" ];   
    return filename, dirpath;
end function;

function ExistsQuarticCMClassNumberDataFile(h,t)
    filename, dirpath := QuarticCMClassNumberFilename(h,t);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, filename * "z"; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, filename * "z"; end if;
    return true, filename * "z";
end function;

function QuarticCMClassNumberDataFile(h,t)
    filename, dirpath := QuarticCMClassNumberFilename(h,t);
    if System("test -d " * dirpath) ne 0 then
        System("mkdir " * dirpath);
    end if;
    System("touch " * filename);
    return filename;
end function;


