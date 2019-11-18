////////////////////////////////////////////////////////////////////////
//                                                                    //  
//                       MODELS FOR MODULAR CURVES                    //
//                               David Kohel                          //
//                             September 2000                         //
//                       Last modified June 2001                      //
//                                                                    // 
////////////////////////////////////////////////////////////////////////

forward DefaultModularCurveX0; // DefaultModularCurveX1;

////////////////////////////////////////////////////////////////////////
//                        MODELS FOR X_0(N)                           //
////////////////////////////////////////////////////////////////////////

intrinsic ModularCurveX0(N::RngIntElt : ModelType := "Default" )
    -> CrvMod {The modular curve X_0(N) of level N.}

    require Type(ModelType) eq MonStgElt :
        "ModelType parameter must be a string.";
    Models := {"Atkin", "Canonical", "Classical", "Default"};
    require ModelType in Models :
        "Invalid ModelType parameter", ModelType;
    return ModularCurveX0(N, Integers() : ModelType := ModelType);
end intrinsic;
   
intrinsic ModularCurveX0(p::RngIntElt,R::Rng :  ModelType := "Default")
    -> CrvMod {The modular curve X_0(p) of level p over R.}

    require Type(ModelType) eq MonStgElt :
        "ModelType parameter must be a string.";
    DatabaseModels := {"Atkin", "Canonical", "Classical"};
    if ModelType in DatabaseModels then
	D := ModularCurveDatabase(ModelType);
	require p in D : "Argument 1 is not in database";
	if Type(R) eq RngInt then
	    D := ModularCurveDatabase("Atkin");
	    X0 := ModularCurve(D,p);
	else 
	    X0 := BaseExtend(ModularCurve(D,p),R);
	end if;
	// X0`Level := p;
	// X0`ModelIndex := 0;
	X0`ModelType := ModelType;
	X0`Genus := ModularGenusX0(p); 
	return X0;
    end if;
    return DefaultModularCurveX0(p,R);
end intrinsic;

function DefaultModularCurveX0(N,R)
   DefaultLevels := {2,3,4,5,7,11,13,17};
   if N notin DefaultLevels then
      error "No data for the default model type of this level.";
   end if;

   P2 := PolynomialRing(R,2);
   u := P2.1; v := P2.2;
   if (N eq 2) then
      F := u*v - 4096;
      X := ModularCurve(AffineSpace(P2),F,"Default",[2,1,1]);
      X`InvolutionImages := [ v, u ];
      X`Genus := 0;
      X`Cusps := [ [1,0,0], [0,1,0] ];
      X`SingularSubscheme := [ u + 64 ];
      X`Eisenstein2 := [ P2 | 1, 6 ];
      X`Eisenstein4 := [ (u + 256), (u+64) ];
      X`Eisenstein6 := [ (u - 512), (u+64) ];
      X`EllipticSurfaces := [ [
         [ -(u + 256), 48*(u+64) ],
         [ -(u - 512), 864*(u+64) ]
      ] ];
      X`ModularInvariants := [
         [ P2 | -1, 6],
         [ P2 | 1, 1]
      ];
      // X`jInvariant := (u + 256)^3/u^2;
   elif (N eq 4) then
      F := u*v - 256;
      X := ModularCurve(AffineSpace(P2),F,"Default",[N,1,1])
;
      X`InvolutionImages := [ v, u ];
      X`Genus := 0;
      // X`Cusps := [ [1,0,0], [0,1,0] ];
      X`SingularSubscheme := [ u*(u + 16) ];
      X`Eisenstein2 := [ P2 | 1, 8 ];
      X`Eisenstein4 := [ u^2 + 256*u + 4096, 1 ];
      X`Eisenstein6 := [ (u + 32)*(u^2 - 512*u - 8192), 1 ];
      X`EllipticSurfaces := [ [
         [ -(u^2 + 256*u + 4096), 48 ],
         [ -(u + 32)*(u^2 - 512*u - 8192), 864 ]
      ] ];
      X`ModularInvariants := [
         [ P2 | -(u^2 - 32*u - 2048), 72 ],
         [ P2 | -(u + 128), 12 ],
         [ P2 | 1, 1]
      ];
      X`jInvariant := [ (u^2 + 256*u + 4096)^3, u^4 * (u + 16) ];  
   elif (N eq 3) then
      F := u*v - 1;
      X := ModularCurve(AffineSpace(P2),F,"Default",[N,1,1])
;
      X`InvolutionImages := [ v, u ];
      X`Genus := 0;
      X`Cusps := [ [1,0,0], [0,1,0] ];
      X`SingularSubscheme := [ u + 1 ];
      X`Eisenstein2 := [ (u+1), 4*u ];
      X`Eisenstein4 :=  [ 9*(u + 9)*(u + 1), u^2 ];
      X`Eisenstein6 := [ 27*(u^2 - 18*u - 27)*(u + 1), u^3 ];
      X`EllipticSurfaces := [ [ 
         [ -3*(u + 9)*(u + 1), 16*u^2 ],
         [ -(u^2 - 18*u - 27)*(u + 1), 32*u^3 ]
      ] ];
      X`ModularInvariants := [  
         [ -3*(u+1), 4*u ],
         [ 1, 1]
      ];
      X`jInvariant := [ 27*(u + 1)*(u + 9)^3, u^3 ];
   elif (N eq 5) then
      F := u*v - 125;
      X := ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]);
      X`InvolutionImages := [ v, u ];
      X`Genus := 0;
      X`Cusps := [ [1,0,0], [0,1,0] ];
      X`SingularSubscheme := [ u^2 + 22*u + 125 ];
      X`Eisenstein2 := [ (u^2 + 22*u + 125), 6*u ];
      X`Eisenstein4 := [ (u^2 + 250*u + 3125)*(u^2 + 22*u + 125), u^2 ];
      X`Eisenstein6 := [ (u^2 - 500*u - 15625)*(u^2 + 22*u + 125)^2, u^3 ];
      X`EllipticSurfaces := [ [
         [ -(u^2 + 250*u + 3125)*(u^2 + 22*u + 125), 48*u^2 ],
         [ -(u^2 - 500*u - 15625)*(u^2 + 22*u + 125)^2, 864*u^3 ]
      ] ];
      X`ModularInvariants := [  
         [ (u^2 + 22*u + 125)*(89*u^2 + 2750*u + 15625), 720*u^2 ],
         [ -5*(u^2 + 22*u + 125), 6*u ],
         [ 1, 1 ]
      ];
      X`jInvariant := [ (u^2 + 250*u + 3125)^3, u^5 ];
   elif (N eq 7) then
      F := u*v - 49;
      X := ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]);
      X`InvolutionImages := [ v, u ];
      X`Genus := 0;
      X`Cusps := [ [1,0,0], [0,1,0] ];
      X`SingularSubscheme := [ u^2 + 13*u + 49 ];
      X`Eisenstein2 := [ (u^2 + 13*u + 49), 4*u ];
      X`Eisenstein4 := [ (u^2 + 245*u + 2401)*(u^2 + 13*u + 49), u^2 ];
      X`Eisenstein6 := [ (u^4 - 490*u^3 - 21609*u^2 - 235298*u - 823543)
 		            *(u^2 + 13*u + 49), u^3 ];
      X`EllipticSurfaces := [ [
         [ -(u^2 + 245*u + 2401)*(u^2 + 13*u + 49), 48*u^2 ],
         [ -(u^4 - 490*u^3 - 21609*u^2 - 235298*u - 823543)
              *(u^2 + 13*u + 49), 864*u^3 ]
      ] ];
      X`ModularInvariants := [  
         [ -(881*u^4 + 38122*u^3 + 525819*u^2 + 3058874*u + 5764801)
            *(u^2 + 13*u + 49), 12096*u^3 ],
         [ (u^2 + 13*u + 49)*(33*u^2 + 637*u + 2401), 48*u^2 ],
         [ -7*(u^2 + 13*u + 49), 4*u ],
         [ 1, 1 ]
      ];
      X`jInvariant := [ (u^2 + 13*u + 49)*(u^2 + 245*u + 2401)^3, u^7 ];
   elif (N eq 11) then
      F := v^2 - (u+1)*(u^3 - 17*u^2 + 19*u - 7);
      X := ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]);
      X`InvolutionImages := [ u, -v ];
      // X`SingularSubscheme := [ P2 | 1 ];
      X`Genus := 1;
      X`Cusps := [ [0,1,0] ]; // Simple double point.
      X`SingularSubscheme := [ 1 ];
      X`Eisenstein2 := [ -5*u + 3, 12 ];
      X`Eisenstein4 := 
         [ (61*u^2 - 246*u + 45) + 60*v, 1 ];
      X`Eisenstein6 := 
         [ (665*u^3 - 5733*u^2 + 1323*u + 945) + (666*u - 918)*v, 1 ]; 
      X`EllipticSurfaces := [ [
	 [ -(61*u^2 - 246*u + 45) - 60*v, 48 ],
         [ -((665*u^3 - 5733*u^2 + 1323*u + 945) + (666*u - 918)*v), 864 ] 
      ] ];
      X`ModularInvariants := [ 
         [ 928945*u^5 - 1319331*u^4 - 33434694*u^3 +
           67821354*u^2 + 20437029*u - 19964151 +  
           (842616*u^3 + 2745576*u^2 - 14143896*u + 12389112)*v,
 	   11*12^5 ],
         [ (13113576*u^2 + 30509136*u - 76808088)*v + 17120089*u^4 +
           1838676*u^3 - 252168714*u^2 + 239568084*u + 3111129,
	   12^4*7*59 ],
         [ 4387*u^3 + 3897*u^2 - 19359*u + 8235 + 
           (2268*u + 2268)*v, 864], 
         [ 108*v + 497*u^2 + 138*u + 81, 72 ],
         [ -11*(-5*u + 3), 12 ],
         [ 1, 1]
      ];
      X`jInvariant := [
         (u^11 - 55*u^10 + 1188*u^9 - 12716*u^8 + 69630*u^7 
            - 177408*u^6 + 133056*u^5 + 132066*u^4 - 187407*u^3  
            + 40095*u^2 + 24300*u - 6750) + 
         (u^9 - 47*u^8 + 843*u^7 - 7187*u^6 + 29313*u^5 - 48573*u^4 
            + 10665*u^3 + 27135*u^2 - 12150*u)*v, 2];
   elif (N eq 13) then
      F := u*v - 13;
      X := ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]);
      X`InvolutionImages := [ v, u ];
      X`Genus := 0;
      X`Cusps := [ [1,0,0], [0,1,0] ];
      X`SingularSubscheme := [ (u^2 + 6*u + 13)*(u^2 + 5*u + 13) ];
      X`Eisenstein2 := [ (u^2 + 5*u + 13)*(u^2 + 6*u + 13), 2*u^2 ];
      X`Eisenstein4 := [ (u^4 + 247*u^3 + 3380*u^2 + 15379*u + 28561) 
	       *(u^2 + 5*u + 13)*(u^2 + 6*u + 13), u^4 ];
      X`Eisenstein6 := 
         [ (u^6-494*u^5-20618*u^4-237276*u^3-1313806*u^2-3712930*u-4826809)
           *(u^2 + 5*u + 13)*(u^2 + 6*u + 13)^2, u^6 ];
      X`EllipticSurfaces := [ [
         [ -(u^4 + 247*u^3 + 3380*u^2 + 15379*u + 28561) 
           *(u^2 + 5*u + 13)*(u^2 + 6*u + 13), 48*u^4 ],
         [ -(u^6-494*u^5-20618*u^4-237276*u^3-1313806*u^2-3712930*u-4826809)
 	   *(u^2 + 5*u + 13)*(u^2 + 6*u + 13)^2, 864*u^6 ]
      ] ];
      X`jInvariant := [ (u^4 + 247*u^3 + 3380*u^2 + 15379*u + 28561)^3
                        *(u^2 + 5*u + 13), u^13 ];
   elif (N eq 17) then
      F := v^2 - (u+1)*(u^3 - 17*u^2 + 19*u - 7);
      X := ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]);
      X`InvolutionImages := [ u, -v ];
      // X`SingularSubscheme := [ P2 | 1 ];
      X`Genus := 1;
      X`Cusps := [ [0,1,0] ]; // Simple double point.
      // X`SingularSubscheme := [ 1 ];
      X`Eisenstein2 := [ ];
      X`Eisenstein4 := [ ];
      X`Eisenstein6 := [ ]; 
      X`EllipticSurfaces := [ ];
      X`ModularInvariants := [ 
         [ 1, 1]
      ];
      X`jInvariant := [ ];
   end if;
   // X`Level := N;
   // X`ModelIndex := 0;
   X`ModelType := "Default";
   return X;
end function;

////////////////////////////////////////////////////////////////////////
//                         MODELS FOR X1(N)                           //
////////////////////////////////////////////////////////////////////////

intrinsic ModularCurveX1(N::RngIntElt) -> Rec
   {Returns the modular curve X_1(N) of level N.}
   Levels := {2,3,4,5,6,7,8,9,10,11};
   require N in Levels : "Modular curve of this level is not stored.";
   return ModularCurveX1(N,Integers());
end intrinsic;

intrinsic ModularCurveX1(N::RngIntElt,K::Rng) -> Rec
    {Returns the modular curve X_1(N) of level N.}
    Levels := {2,3,4,5,6,7,8,9,10,11};
    require N in Levels : "Modular curve of this level is not stored.";
    if (N eq 2) then
	P2 := PolynomialRing(K,2);
	u := P2.1; v := P2.2;
        F := u - v; // Dummy relation.
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ [0,0,1], [1,0,64] ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ P2 | ];
        X`CharacterGenerators := [ Integers() | ];
        X`CharacterImages := [ ];
        X`EllipticSurfaces := [ [
            [ 1, 1 ],
            [ 0, 1 ],
            [ 0, 1 ],
            [ u, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 3) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u - v;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`CharacterGenerators := [ 2 ];
        X`CharacterImages := [ [ 0, -u ] ];
        X`EllipticSurfaces := [ [
            [ 1, 1 ],
            [ 0, 1 ],
            [ u, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 4) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u - v;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`CharacterGenerators := [ -1 ];
        X`CharacterImages := [ [ 0, -u ] ];
        X`EllipticSurfaces := [ [
            [ 1, 1 ],
            [ u, 1 ],
            [ u, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 5) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u - v - 1;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`CharacterGenerators := [ 2 ];
        X`CharacterImages := [ [-v,v^2,1] ];
        X`EllipticSurfaces := [ [
            [ u, 1 ],
            [ v, 1 ],
            [ v, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 6) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u^2 - 3*u + v + 2;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`CharacterGenerators := [ -1 ];
        X`CharacterImages := [ [-v,v*(u-1)] ];
        X`EllipticSurfaces := [ [
            [ u, 1 ],
            [ v, 1 ],
            [ v, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 7) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u - v + v^2;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`CharacterGenerators := [ 3 ];
        X`CharacterImages := [ [ -u , -v + 1, u^2 ] ];
        X`EllipticSurfaces := [ [
            [ u+1, u ],
            [ v, u ],
            [ v, u^2 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 8) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u^2*v + u^2 - 5*u*v - 2*u + 2*v^2 + 4*v + 1;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`CharacterGenerators := [ -1, 5 ];
        X`CharacterImages := [ [0,-v,1], [-u+1,u^2-2*u+1,1] ];
        X`EllipticSurfaces := [ [
            [ u, 1 ],
            [ v, 1 ],
            [ v, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 9) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u^5 - 6*u^4 + u^3*v + 15*u^3 - 6*u^2*v - 19*u^2 
        + 3*u*v^2 + 9*u*v + 12*u - v^3 - 3*v^2 - 4*v - 3;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`EllipticSurfaces := [ [
            [ u, 1 ],
            [ v, 1 ],
            [ v, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 10) then
        P2 := PolynomialRing(K,2); 
        u := P2.1; v := P2.2;
        F := u*(u+1)*v - 1;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 0;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`EllipticSurfaces := [ [
            [ (2*u^3 + 2*u^2 - 2*u - 1)*v, 1 ],
            [ (2*u + 1)*u^2*v, 1 ],
            [ -(2*u+1)*(u^2+3*u+1)*u^2*v^2, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    elif (N eq 11) then
        P2 := PolynomialRing(K,2);
        u := P2.1; v := P2.2;
        F := u^3 - u^2 - v^2 + v;
	X := ProjectiveClosure(
	    ModularCurve(AffineSpace(P2),F,"Default",[N,1,1]));
        // X`Level := N;
        // X`ModelIndex := 1;
        X`ModelType := "Default";
        X`Genus := 1;
        X`Cusps := [ ];
        X`AffinePolynomial := F;
        X`SingularSubscheme := [ ];
        X`CharacterGenerators := [ 3 ];
        X`CharacterImages := [ [-u+1,u-v-1,1] ];
        X`EllipticSurfaces := [ [
            [ u, 1 ],
            [ v, 1 ],
            [ v, 1 ],
            [ 0, 1 ], 
            [ 0, 1 ]
        ] ];
        X`ModularPoint := [ [0,0,1] ];
        return X;
    end if;
    return X;
end intrinsic;

