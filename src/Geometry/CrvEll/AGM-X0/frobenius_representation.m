////////////////////////////////////////////////////////////////////////
//                                                                    //
//                            David Kohel                             //
//                    Parametrized Representations                    //
//                       of Frobenius Isogeny                         //
//                       and Norm computation                         //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function AGMFrobeniusNorm(N,p,x)
    case [N,p]:
    when [2,2]:
        y := FrobeniusImage(x);
        // Square of Frobenius:
        // Num := (256*y+1)*(-256*y*(256*y+1)+16*x+1);
        // Den := (256*x+1)*(512*y*(64*y+1)-8*x+1);
        // Using the fact that Norm(256*y+1) = Norm(256*x+1):
        Num := (-256*y*(256*y+1)+16*x+1);
        Den := (512*y*(64*y+1)-8*x+1);
        return Exp(Trace(Log(Num div Den)) div 2);
    when [4,2]:
        // Square of Frobenius:
        // Num := 32*y+1;
        // Den := 8*x+1; 
        // But since Norm(32*y+1) = Norm(32*x+1):
        return Exp(Trace(Log((1+32*x) div (1+8*x))) div 2);
    when [8,2]:
        // Minimizing degrees:
        // Num := 2*(4*y+1)*x-1;
        // Den := 2*(4*y+1)*x+1;
        // or (exploiting cancellation):
        // Num := (-4*x+1)*(4*y+1);
        // Den := 4*y-1;
        // But since Norm(-4*x+1) = Norm(-4*y+1):
        return Exp(Trace(Log(1+4*x)));
    when [16,2]:
        // Use that the square of x is the function of level 8:
        return Exp(Trace(Log(1+4*x^2)));
    when [3,3]:
        // Square of Frobenius:
        Num := (3*x+1)*(-19683*x^2-486*x+1);
        Den := (243*x+1)*(-27*x^2+18*x+1);
        return Exp(Trace(Log(Num div Den)) div 2);
    when [9,3]:
        // Square of Frobenius:
        g := (27*x^2+9*x+1);
        Num := (3*x+1)*(27*x^2+1)*(-243*(81*x^2*g^2+2*x*g)+1);
        Den := (-27*x^2+1)*(243*g*x+1)*(27*x^2+g^2);
        return Exp(Trace(Log(Num div Den)) div 2);
    when [5,5]:
        // Square of Frobenius:
        x2 := 5^2*x; x3 := 5*x2;
        Num := (5*(x + 2)*x + 1)*(-x3^2 - 4*x3 + 1);
        Den := (5*(x2 + 2)*x2 + 1)*(-x^2 + 4*x + 1);
        // Log doesn't converge, so we have to call Norm:
        return Sqrt(Norm(Num div Den));
    when [25,5]:
        // Square of Frobenius...
        x := 25*x^5 + 25*x^4 + 15*x^3 + 5*x^2 + x;
        x2 := 5^2*x; x3 := 5*x2;
        Num := (5*(x + 2)*x + 1)*(-x3^2 - 4*x3 + 1);
        Den := (5*(x2 + 2)*x2 + 1)*(-x^2 + 4*x + 1);
        // Log doesn't converge, so we have to call Norm:
        return Sqrt(Norm(Num div Den));
    when [7,7]:
        // Square of Frobenius...
        x2 := 7^2*x;
        Num := (x^2 + 5*x + 1)*(-7^7*x^4 - (2*x2^2 + 9*x2 + 10)*x2 + 1);
        Den := (x2^2 + 5*x2 + 1)*(-7*x^4 + 7*(10*x^2 + 9*x + 2)*x + 1);
        // Log doesn't converge, so we have to call 'Norm'.
        return Sqrt(Norm(Num div Den));
    when [13,13]:
        // Square of Frobenius...
        Num := (x^4 + 19*x^3 + 20*x^2 + 7*x + 1)* 
            (-((13*x)^6 + 10*(13*x)^5 + 46*(13*x)^4
            + 108*(13*x)^3 + 122*(13*x)^2 + 38*(13*x)) + 1);
        Den := ((13*x)^4 + 7*(13*x)^3 + 20*(13*x)^2 + 19*(13*x) + 1)*
            (-x^6 + 38*x^5 + 122*x^4 + 108*x^3 + 46*x^2 + 10*x + 1);
        // Log doesn't converge, so we have to call 'Norm'.
        return Sqrt(Norm(Num div Den));
    end case;
end function;

