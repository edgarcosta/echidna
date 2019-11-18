////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                    Parametrized Representations                    //
//                       of Frobenius Isogeny                         //
//                       and Norm computation                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function SatohFrobeniusNorm(p,x)
    case p:
    when 2:
        // Square of Frobenius:
        y := FrobeniusImage(x);
        Num := (-256*y*(256*y+1)+16*x+1);
        Den := (512*y*(64*y+1)-8*x+1);
        return Exp(Trace(Log(Num div Den)) div 2);
    when 3:
        // Square of Frobenius:
        Num := (3*x+1)*(-19683*x^2-486*x+1);
        Den := (243*x+1)*(-27*x^2+18*x+1);
        return Exp(Trace(Log(Num div Den)) div 2);
    when 5:
        // Square of Frobenius:
        x2 := 5^2*x; x3 := 5*x2;
        Num := (5*(x + 2)*x + 1)*(-x3^2 - 4*x3 + 1);
        Den := (5*(x2 + 2)*x2 + 1)*(-x^2 + 4*x + 1);
        // Log doesn't converge, so we have to call Norm:
        return Sqrt(Norm(Num div Den));
    when 7:
        // Square of Frobenius:
        x2 := 7^2*x;
        Num := (x^2 + 5*x + 1)*(-7^7*x^4 - (2*x2^2 + 9*x2 + 10)*x2 + 1);
        Den := (x2^2 + 5*x2 + 1)*(-7*x^4 + 7*(10*x^2 + 9*x + 2)*x + 1);
        // Log doesn't converge, so we have to call 'Norm'.
        return Sqrt(Norm(Num div Den));
    when 11:
        // Square of Frobenius:
	return x;
    when 13:
        // Square of Frobenius:
        Num := (x^4 + 19*x^3 + 20*x^2 + 7*x + 1)* 
            (-((13*x)^6 + 10*(13*x)^5 + 46*(13*x)^4
            + 108*(13*x)^3 + 122*(13*x)^2 + 38*(13*x)) + 1);
        Den := ((13*x)^4 + 7*(13*x)^3 + 20*(13*x)^2 + 19*(13*x) + 1)*
            (-x^6 + 38*x^5 + 122*x^4 + 108*x^3 + 46*x^2 + 10*x + 1);
        // Log doesn't converge, so we have to call 'Norm'.
        return Sqrt(Norm(Num div Den));
    end case;
end function;

