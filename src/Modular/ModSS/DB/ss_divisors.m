//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                        SUPERSINGULAR DIVISORS DATABASE                   //
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

DATDIR := GetEchidnaDatabaseRoot() * "/DivSS/";
prime_length := 8;

//////////////////////////////////////////////////////////////////////////////

forward SupersingularDataFile, SupersingularWrite;
forward IsInSupersingularDomain, ExistsSupersingularDataFile;

//////////////////////////////////////////////////////////////////////////////
//                          CREATION FUNCTION                               //
//////////////////////////////////////////////////////////////////////////////

intrinsic SupersingularDivisorsDatabase() -> DBUser
    {The database of supersingular divisors.}
    Dat := New(DBUser);
    Dat`DBIdentifier := "Supersingular divisors";
    Dat`WriteFunction := SupersingularWrite;
    Dat`ExistsFunction := ExistsSupersingularDataFile;
    Dat`IsInDomainFunction := IsInSupersingularDomain;
    return Dat;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             READ ACCESS                                  //
//////////////////////////////////////////////////////////////////////////////

intrinsic SupersingularPolynomials(Dat::DBUser, p::RngIntElt) -> SetIndx
    {The indexed set of supersingular divisors over F_p.}
        
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be a database of supersingular divisors.";
    require IsPrime(p) : "Argument 2 must be prime.";
    bool, filename := ExistsSupersingularDataFile(<"pol",p>);
    require bool : "Argument 1 contains no data for this characteristic.";
    file := POpen("bunzip2 -c " * filename, "r");   
    F := FiniteField(p);
    P := PolynomialRing(F); x := P.1;
    SS := {@ @};
    strseq := Gets(file);
    while not IsEof(strseq) do
        Include(~SS,P!StringToIntegerSequence(strseq));
	strseq := Gets(file);
    end while;
    return SS;
end intrinsic;

intrinsic SupersingularNormGrams(Dat::DBUser, p::RngIntElt) -> SetIndx
    {The indexed set of supersingular divisors over F_p.}
        
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be a database of supersingular divisors.";
    require IsPrime(p) : "Argument 2 must be prime.";
    bool, filename := ExistsSupersingularDataFile(<"nrm",p>);
    require bool : "Argument 1 contains no data for this characteristic.";
    file := POpen("bunzip2 -c " * filename, "r");   
    grams := {@ @}; 
    strseq := Gets(file);
    while not IsEof(strseq) do
	Include(~grams,SymmetricMatrix(StringToIntegerSequence(strseq)));
	strseq := Gets(file);
    end while;
    return grams;
end intrinsic;

intrinsic SupersingularDiscriminantGrams(Dat::DBUser, p::RngIntElt) -> SetIndx
    {The indexed set of supersingular divisors over F_p.}
        
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be a database of supersingular divisors.";
    require IsPrime(p) : "Argument 2 must be prime.";
    bool, filename := ExistsSupersingularDataFile(<"dsc",p>);
    require bool : "Argument 1 contains no data for this characteristic.";
    file := POpen("bunzip2 -c " * filename, "r");   
    grams := {@ @}; 
    strseq := Gets(file);
    while not IsEof(strseq) do
	Include(~grams,SymmetricMatrix(StringToIntegerSequence(strseq)));
	strseq := Gets(file);
    end while;
    return grams;
end intrinsic;

intrinsic SupersingularDualDiscriminantGrams(
    Dat::DBUser, p::RngIntElt) -> SetIndx
    {}
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be a database of supersingular divisors.";
    require IsPrime(p) : "Argument 2 must be prime.";
    bool, filename := ExistsSupersingularDataFile(<"dds",p>);
    require bool : "Argument 1 contains no data for this characteristic.";
    file := POpen("bunzip2 -c " * filename, "r");   
    grams := {@ @}; 
    strseq := Gets(file);
    while not IsEof(strseq) do
	Include(~grams,SymmetricMatrix(StringToIntegerSequence(strseq)));
	strseq := Gets(file);
    end while;
    return grams;
end intrinsic;

intrinsic SupersingularTernarySeries(Dat::DBUser, p::RngIntElt) -> SetIndx
    {}
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be a database of supersingular divisors.";
    require IsPrime(p) : "Argument 2 must be prime.";
    bool, filename := ExistsSupersingularDataFile(<"ser",p>);
    require bool : "Argument 1 contains no data for this characteristic.";
    file := POpen("bunzip2 -c " * filename, "r");   
    P := PowerSeriesRing(IntegerRing());
    prec := StringToInteger(Gets(file));
    OERR := BigO(P.1^prec);
    theta := {@ @}; 
    strseq := Gets(file);
    while not IsEof(strseq) do
	Include(~theta,P!StringToIntegerSequence(strseq)+OERR);
	strseq := Gets(file);
    end while;
    return theta;
end intrinsic;

intrinsic SupersingularDualTernarySeries(
    Dat::DBUser, p::RngIntElt) -> SetIndx
    {}
    require Dat`DBIdentifier eq "Supersingular divisors" : 
        "Argument 1 must be a database of supersingular divisors.";
    require IsPrime(p) : "Argument 2 must be prime.";
    bool, filename := ExistsSupersingularDataFile(<"srd",p>);
    require bool : "Argument 1 contains no data for this characteristic.";
    file := POpen("bunzip2 -c " * filename, "r");   
    P := PowerSeriesRing(IntegerRing());
    prec := StringToInteger(Gets(file));
    OERR := BigO(P.1^prec);
    theta := {@ @}; 
    strseq := Gets(file);
    while not IsEof(strseq) do
	Include(~theta,P!StringToIntegerSequence(strseq)+OERR);
	strseq := Gets(file);
    end while;
    return theta;
end intrinsic;

//////////////////////////////////////////////////////////////////////////////
//                             WRITE ACCESS                                 //
//////////////////////////////////////////////////////////////////////////////

procedure SupersingularPolynomialsWrite(SS,p)
    // {Write the indexed set SS to the class polynomial database.}
    filename := SupersingularDataFile("pol",p);
    file := Open(filename,"w");   
    Flush(file);
    for h in SS do
	Puts(file,&*[ Sprint(c) * " " : c in Eltseq(h) ]);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

procedure SupersingularNormGramsWrite(SS,p)
    filename := SupersingularDataFile("nrm",p);
    file := Open(filename,"w");   
    Flush(file);
    for A in SS do
	S := &cat[ [ A[i,j] : j in [1..i] ] : i in [1..4] ];
	matstr := &*[ IntegerToString(x) * " " : x in S ];
	Puts(file,matstr);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

procedure SupersingularDiscriminantGramsWrite(SS,p)
    filename := SupersingularDataFile("dsc",p);
    file := Open(filename,"w");   
    Flush(file);
    for A in SS do
	S := &cat[ [ A[i,j] : j in [1..i] ] : i in [1..3] ];
	matstr := &*[ IntegerToString(x) * " " : x in S ];
	Puts(file,matstr);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

procedure SupersingularDualDiscriminantGramsWrite(SS,p)
    filename := SupersingularDataFile("dds",p);
    file := Open(filename,"w");   
    Flush(file);
    for A in SS do
	S := &cat[ [ A[i,j] : j in [1..i] ] : i in [1..3] ];
	matstr := &*[ IntegerToString(x) * " " : x in S ];
	Puts(file,matstr);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

procedure SupersingularTernarySeriesWrite(SS,p: Precision := 0)
    prec := Precision eq 0 select RelativePrecision(SS[1]) else Precision;
    filename := SupersingularDataFile("ser",p);
    file := Open(filename,"w");   
    Flush(file);
    Puts(file,Sprint(prec));
    for f in SS do
	Puts(file,&*[ Sprint(x) * " " : x in Eltseq(f) ]);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;
    
procedure SupersingularDualTernarySeriesWrite(SS,p: Precision := 0)
    prec := Precision eq 0 select RelativePrecision(SS[1]) else Precision;
    filename := SupersingularDataFile("srd",p);
    file := Open(filename,"w");   
    Flush(file);
    Puts(file,Sprint(prec));
    for f in SS do
	Puts(file,&*[ Sprint(x) * " " : x in Eltseq(f) ]);
    end for;
    delete file;
    System("bzip2 -c " * filename * " > " * filename * "z");
    System("chmod a+r " * filename * "z");
    System("rm " * filename);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                            FILE STRUCTURE                                //
//////////////////////////////////////////////////////////////////////////////

function SupersingularDataFilename(prefix,p)
    prime := IntegerToString(p);   
    while #prime lt prime_length do prime := "0" cat prime; end while;
    filename := &*[ DATDIR, prefix, ".", prime, ".db" ];
    return filename;
end function;

function IsInSupersingularDomain(X)
    string := X[1]; p := X[2];
    if not Type(string) eq MonStgElt and Type(p) eq RngIntElt then
	return false, "Argument must be an tuple consisting of a string and an integer.";
    end if;
    return true, "";
end function;

function ExistsSupersingularDataFile(X)
    // Returns true if and only if the compressed data file 
    // exists, and if so, returns the filename for reading.
    string := X[1]; p := X[2];
    filename := SupersingularDataFilename(string,p);
    t := System("test -f " * filename * "z");
    if t ne 0 then return false, _; end if;
    return true, filename * "z";
end function;

function SupersingularDataFile(string,p)
    // Creates the file and returns its name.
    filename := SupersingularDataFilename(string,p);
    t := System("test -d " * DATDIR);
    if t ne 0 then System("mkdir " * DATDIR); end if;
    System("touch " * filename);
    return filename;
end function;
