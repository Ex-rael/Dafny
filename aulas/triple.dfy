// methods, funções executáveis
//method Triple(x: int) returns (r: int)
//requires true // pre condicao
//ensures r == 3 * x // pos condicao
//{
//    var y := 2*x;
//    r := x + y;
//}


method Mult(a: int, b: int) returns (r: int)
requires a > 0 && b >= 0
ensures r == a * b
{
    var j := a;
    var k := b;
    r := 0;
    while j > 0
    invariant r + ( j * k) == a * b
    {
       r := r + k;
       j := j - 1;
    }
    
}

method Pot(x: int, y: int) returns (a: int)
requires x > 0 && y >= 0
ensures a == x  y
{
    var i := y;
    a := 1;
    while i > 0
    invariant a == x ^ (y - i) && i >= 0
    {
        a := Mult(a, x);
        i := i - 1;
    }    
}