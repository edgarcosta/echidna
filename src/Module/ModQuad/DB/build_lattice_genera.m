//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//                     LATTICE DATABASE CONSTRUCTOR                         //
//                                                                          //
//////////////////////////////////////////////////////////////////////////////

intrinsic BuildLatticeDatabase(Dat::DBUser,r::RngIntElt,S::[RngIntElt])
    {Build the database of genera of lattices of rank r and 
    determinant in S.}
    require Dat`DBIdentifier eq "Lattice genera" :
        "Argument 1 must be the database of lattice genera.";
    require r eq 2 : "Only implemented for r = 2";
    for det in S do
        D := -det; 
        c := 1;
        if D mod 4 in {2,3} then
            D *:= 4;
            c := 2;
        end if; 
        QF := BinaryQuadraticForms(D);
        RF := ReducedForms(QF);
        GF := {@ f^2 : f in RF @};      
        gen_seq := [ GF ]; 
        t := Integers()!(#RF/#GF);
        while #gen_seq lt t do
            f := Random(RF); 
            if not &or[ f in H : H in gen_seq ] then
                Append(~gen_seq,{@ f*g : g in GF @});
            end if;  
        end while;
        genera := [ ];
        for Gseq in gen_seq do
            S := [ ScaledLattice(Lattice(f),1/c) : f in Gseq ];
            G := Genus(S[1]);         
            G`Representatives := S;         
            Append(~genera,G);
        end for;
        Write(Dat,genera : Overwrite := true);
    end for;
end intrinsic;

