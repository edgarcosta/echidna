//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                       MODULAR POLYNOMIALS DATABASE                       //
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

/* Created by David Kohel, September 2000 */

DATDIR := GetEchidnaDatabaseRoot() * "/PolMod/";
prefix := "pol";
level_length := 3;
prime_length := 9;
power_length := 6;

//////////////////////////////////////////////////////////////////////////////

forward IsInModularPolynomialDomain, ModularPolynomialWrite;
forward ModularPolynomialDataFile, LocalModularPolynomialDataFile;
forward ExistsModularPolynomialDataFile, ExistsLocalModularPolynomialDataFile;
forward LocalModularPolynomialFilename;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic ModularPolynomialDatabase() -> DBUser
    {The database of modular polynomials.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Modular polynomial";
    Dat`WriteFunction := ModularPolynomialWrite;
    Dat`ExistsFunction := ExistsModularPolynomialDataFile;
    Dat`IsInDomainFunction := IsInModularPolynomialDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                       MODULAR POLYNOMIAL ACCESS                          //
//////////////////////////////////////////////////////////////////////////////

function ModularModularPolynomial(Dat,ModelType,N)
    // Some access function here...
    // Find what primes have already been computed...
    _, dirpath := LocalModularPolynomialFilename(ModelType,N,2);
    loc_prms := [];
    FILES := POpen("find " * dirpath * " -name \"*.dbz\"", "r");
    file := Gets(FILES);
    while not IsEof(file) do
        split_str := Split(file,"/");
        _, _, p, e := Explode(Split(split_str[#split_str],"."));
        p := StringToInteger(p);
        e := e eq "dbz" select 1 else StringToInteger(e);
        Append(~loc_prms,<p,e>);
        file := Gets(FILES);
    end while;
    PZ := PolynomialRing(IntegerRing(),2 : Global);
    Phi := PZ!0; M := 1;
    stable1 := false;
    stable2 := false;
    for pr in loc_prms do
        p := pr[1]; e := pr[2]; q := p^e;
        vprint ModularPolynomial : "Reading local data for q =", q;
        FF := e eq 1 select FiniteField(p) else pAdicQuotientRing(p,e);
        Phi_prev := Phi;
        Psi := ModularPolynomial(Dat,ModelType,N,FF);
        r := InverseMod(M,q);
        Phi +:= r*M*PZ!(Psi-Parent(Psi)!Phi); M *:= q;
        // Phi := NormalForm(Phi,ideal< PZ | M >);
        Phi := &+[ BalancedMod(MonomialCoefficient(Phi,mon),M)*mon : mon in Monomials(Phi) ];
        if GetVerbose("ModularPolynomial") gt 1 then
            Mons := Monomials(Phi);
            num_stable := #[ 1 : mon in Mons | MonomialCoefficient(Phi_prev,mon) eq MonomialCoefficient(Phi,mon) ];
            printf "[%6o] Number of stable coefficients: %o/%o\n", q, num_stable, #Mons;
        end if;
        stable1 := stable2;
	stable2 := Phi_prev eq Phi;
	if stable1 and stable2 then
	    break;
	end if;
    end for;
    return Phi, M, stable1;
end function;

function ModularPolynomialCRT(
    Dat, ModelType, N : Extend := false, InitialPrime := 0, ModularBits := 9)
    ZZ := IntegerRing();
    PZ := PolynomialRing(IntegerRing(),2 : Global);
    if InitialPrime ne 0 then
        p := InitialPrime;
    else
        p := 2^ModularBits;
    end if;
    if p gt 2^20 then
        p := InitialPrime;
        NextModularPrime := PreviousPrime;
    else
        p := InitialPrime;
        NextModularPrime := NextPrime;
    end if;
    exps := {@ @};
    num_stable := 0;
    Phi := PZ!0; M := 1;
    if Extend then
        Phi, M, stable := ModularModularPolynomial(Dat,ModelType,N);
    else
        Phi := PZ!0; M := 1; stable := false;
    end if;
    coeff := MonomialCoefficient;
    stable1 := stable;
    stable2 := stable;
    while not (stable1 and stable2) do
        p := NextModularPrime(p);
        while N mod p eq 0 or M mod p eq 0 do p := NextPrime(p); end while;
        m := Max(ModularBits div Ceiling(Log(2,p)),1); q := p^m;
        if <ModelType,N,q> notin Dat then
            if Extend then
                BuildLocalModularPolynomialDatabase(Dat,ModelType,N,[q]);
            else
                break;
            end if;
        end if;
        if m eq 1 then
            FF := FiniteField(p);
        else
            FF := pAdicQuotientRing(p,m);
        end if;
        Phi_prev := Phi;
        Psi := ModularPolynomial(Dat,ModelType,N,FF);
        r := InverseMod(M,q);
        Phi +:= r*M*PZ!(Psi-Parent(Psi)!Phi); M *:= q;
        Phi := &+[ BalancedMod(MonomialCoefficient(Phi,mon),M)*mon : mon in Monomials(Phi) ];
        if GetVerbose("ModularPolynomial") gt 0 then
            Mons := Monomials(Phi);
            num_stable := #[ 1 : mon in Mons | MonomialCoefficient(Phi_prev,mon) eq MonomialCoefficient(Phi,mon) ];
            printf "[%6o] Number of stable coefficients: %o/%o\n", q, num_stable, #Mons;
        end if;
        stable1 := stable2;
        stable2 := Phi_prev eq Phi;
    end while;
    return Phi, stable1 and stable2;
end function;

intrinsic ModularPolynomial(Dat::DBUser, ModelType::MonStgElt, N::RngIntElt :
    Al := "Global", Extend := false, InitialPrime := 0, ModularBits := 9) -> RngMPolElt
    {The modular polynomial of model ModelType and level N.}

    require Dat`DBIdentifier eq "Modular polynomial" : 
        "Argument 1 must be a database of modular polynomials.";
    require ModelType in {"Atkin","Dedekind eta","Classical", "Reduced Dedekind eta", "Reduced Classical"} :
        "Argument 2 specifies an unrecognized model type.";
    if Al in {"Local", "Modular"} then
        Phi, stable := ModularPolynomialCRT(Dat,ModelType,N : 
            Extend := Extend, InitialPrime := InitialPrime, ModularBits := ModularBits);
        require stable : "Modular data for arguments does not determine global polynomial.";
        return Phi;
    end if;
    require Al eq "Global" : "Parameter Al must be \"Global\", \"Local\", or \"Modular\".";
    bool, filename := ExistsModularPolynomialDataFile(<ModelType,N>);
    require bool :
        "Argument 1 contains no datafile for this model type and level.";
    P2 := PolynomialRing(Integers(),2 : Global);
    X := P2.1; Y := P2.2;
    if N eq 1 then return X-Y; end if;
    file := POpen("bunzip2 -c " * filename, "r");
    strseq := Gets(file);
    Phi := P2!0;
    classical :=  ModelType in {"Classical","Reduced Classical"};
    while not IsEof(strseq) do
        i, j, c := Explode(StringToIntegerSequence(strseq));
        if classical and i ne j then
            Phi +:= c*(X^i*Y^j + X^j*Y^i);
        else
            Phi +:= c*X^i*Y^j;
        end if;
        strseq := Gets(file);
    end while;
    return Phi;
end intrinsic; 


intrinsic ModularPolynomial(Dat::DBUser,
    ModelType::MonStgElt,N::RngIntElt,R::Rng) -> RngMPolElt
    {The modular polynomial of model ModelType and level N over the ring R.}

    require Dat`DBIdentifier eq "Modular polynomial" : 
        "Argument 1 must be a database of modular polynomials.";
    require ModelType in {"Atkin","Dedekind eta","Classical", "Reduced Dedekind eta", "Reduced Classical", "Weber"} :
        "Argument 2 specifies an unrecognized model type.";
    case Type(R):
    when FldFin:
        p := Characteristic(R);
        bool, filename := ExistsLocalModularPolynomialDataFile(<ModelType,N,p>);
    when RngPadRes:
        p := ResidueCharacteristic(R);
        m := Precision(R);
        q := p^m;
        bool, filename := ExistsLocalModularPolynomialDataFile(<ModelType,N,q>);
    else
        bool, filename := ExistsModularPolynomialDataFile(<ModelType,N>);
    end case;
    require bool :
        "Argument 1 contains no datafile for this model type and level.";
    P2 := PolynomialRing(R,2 : Global);
    X := P2.1; Y := P2.2;
    if N eq 1 then return X-Y; end if;
    file := POpen("bunzip2 -c " * filename, "r");   
    strseq := Gets(file);
    Phi := P2!0;
    classical :=  ModelType in {"Classical","Reduced Classical"};
    while not IsEof(strseq) do
        i, j, c := Explode(StringToIntegerSequence(strseq));
        if classical and i ne j then
            Phi +:= c*(X^i*Y^j + X^j*Y^i);
        else
            Phi +:= c*X^i*Y^j;
        end if;
        strseq := Gets(file);
    end while;
    return Phi;
end intrinsic; 


//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure ModularPolynomialWrite(X,Phi)
    // {Write Phi to the modular polynomial database.}
    if Type(X) ne Tup or #X notin {2,3} then
        error if true, "Argument must be a tuple of length 2 or 3.";
    end if;
    ModelType := X[1];
    if not Type(ModelType) eq MonStgElt then
        error if true, "Argument component 1 must be a string.";
    end if;
    N := X[2];
    if not Type(N) eq RngIntElt then
        error if true, "Argument component 2 must be an integer.";
    end if;
    Models := {"Atkin", "Dedekind eta", "Classical", "Reduced Dedekind eta", "Reduced Classical"};
    error if ModelType notin Models, "Modular polynomial model type not recognized.";
    R := BaseRing(Parent(Phi));
    case Type(R):
    when RngInt:
        filename := ModularPolynomialDataFile(ModelType,N);
    when FldFin:
        p := Characteristic(R);
        error if p ne #R,
            "Argument 2 must be defined over the integers or a finite prime field.";
        error if #X eq 3 and X[3] ne #R,
            "Argument 2 must be defined over the prime field specified by component 3 of argument 1.";
        filename := LocalModularPolynomialDataFile(ModelType,N,p);
    when RngPadRes:
        p := ResidueCharacteristic(R);
        m := Precision(R);
        q := p^m;
        error if #X eq 3 and X[3] ne q,
            "Argument 2 must be defined over the prime field specified by component 3 of argument 1.";
        filename := LocalModularPolynomialDataFile(ModelType,N,q);
    else
        error if true,
            "Argument 2 must be defined over the integers or a finite prime field.";
    end case;
    file := Open(filename,"w");
    // Empty the contents of the file, in case it did exist.
    Flush(file);
    // First line is the gram matrix of order 1.
    classical := ModelType in {"Classical","Reduced Classical"};
    ZZ := IntegerRing();
    for m in Monomials(Phi) do
        i, j := Explode(Exponents(m));
        if i ge j or not classical then
            monseq := [i,j] cat [ ZZ!MonomialCoefficient(Phi,m) ];
            Puts(file,&*[ IntegerToString(x) * " " : x in monseq ]);
        end if;
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function ModularPolynomialFilename(ModelType,N)
    level := IntegerToString(N);
    while #level lt level_length do level := "0" cat level; end while;
    case ModelType:
    when "Atkin": model := "Atk";
    when "Dedekind eta": model := "Eta";
    when "Classical": model := "Cls";
    when "Reduced Classical": model := "ClsRed";
    when "Reduced Dedekind eta": model := "EtaRed";
    when "Weber": model := "Wbr";
    else error if true,
        "ModelType must be in {\"Atkin\",\"Dedekind eta\", \"Classical\", \"Reduced Classical\", \"Reduced Dedekind eta\"}";
    end case;
    dirpath := &*[ DATDIR, model, "/" ];
    filename := &*[ dirpath, prefix, ".", level, ".db" ];
    return filename, dirpath;
end function;

function LocalModularPolynomialFilename(ModelType,N,q)
    bool, p, m := IsPrimePower(q);
    error if not bool, "Argument 3 must be a prime power in ModularPolynomialFilename.";
    level := IntegerToString(N);
    prime := IntegerToString(p);
    while #level lt level_length do level := "0" cat level; end while;
    while #prime lt prime_length do prime := "0" cat prime; end while;
    case ModelType:
    when "Atkin": model := "Atk";
    when "Dedekind eta": model := "Eta";
    when "Classical": model := "Cls";
    when "Reduced Classical": model := "ClsRed";
    when "Reduced Dedekind eta": model := "EtaRed";
    when "Weber": model := "Wbr";
    else error if true,
        "ModelType must be in {\"Atkin\",\"Dedekind eta\", \"Classical\", \"Reduced Classical\", \"Reduced Dedekind eta\"}";
    end case;
    dirpath := &*[ DATDIR, model, "/", prefix, ".", level ];
    if m eq 1 then
        filename := &*[ dirpath, "/", prefix, ".", level, ".", prime, ".db" ];
    else
        power := IntegerToString(m);
        while #power lt power_length do power := "0" cat power; end while;
        filename := &*[ dirpath, "/", prefix, ".", level, ".", prime, ".", power, ".db" ];
    end if;
    return filename, dirpath;
end function;

function IsInModularPolynomialDomain(X)
    if Type(X) ne Tup or #X notin {2,3} then
        return false, "Argument must be a tuple of length 2 or 3.";
    end if;
    ModelType := X[1];
    if not Type(ModelType) eq MonStgElt then
        return false, "Argument component 1 must be a string.";
    end if;
    N := X[2];
    if not Type(N) eq RngIntElt then
        return false, "Argument component 2 must be an integer.";
    end if;
    if #X eq 3 and not Type(X[3]) eq RngIntElt then
        return false, "Argument component 3 must be an integer.";
    end if;
    return true, "";
end function;

function ExistsModularPolynomialDataFile(X)
    // Returns true if and only if the compressed data file
    // exists, and if so, returns the file handle for reading.
    ModelType := X[1]; N := X[2];
    if #X eq 2 then
        filename, dirpath := ModularPolynomialFilename(ModelType,N);
    else
        filename, dirpath := LocalModularPolynomialFilename(ModelType,N,X[3]);
    end if;
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function ExistsLocalModularPolynomialDataFile(X)
    // Returns true if and only if the compressed data file
    // exists, and if so, returns the file handle for reading.
    ModelType := X[1]; N := X[2]; q := X[3];
    filename, dirpath := LocalModularPolynomialFilename(ModelType,N,q);
    t := System("test -d " * dirpath);
    if t ne 0 then return false, _; end if;
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function ModularPolynomialDataFile(ModelType,N)
    filename, dirpath := ModularPolynomialFilename(ModelType,N);
    if System("test -d " * dirpath) ne 0 then
        System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;

function LocalModularPolynomialDataFile(ModelType,N,q)
    filename, dirpath := LocalModularPolynomialFilename(ModelType,N,q);
    if System("test -d " * dirpath) ne 0 then
        System(&*[ "mkdir ", dirpath]);
    end if;
    System("touch " * filename);
    return filename;
end function;
