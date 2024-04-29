function Pot(a:nat, b:nat):nat
{
    if (b == 0)
    then 1
    else a * Pot(a, b-1)
}

predicate Par(n:nat)
{
    n % 2 == 0
}

method PotenciaRapida(a:nat, b:nat) returns (r:nat)
  ensures r == Pot(a,b)
{
    var c := a;
    var i := b;
    r := 1;
    while i > 0
      invariant 0 <= i <= b
      invariant r * Pot(c,i) == Pot(a,b)
    {
        PotLema(c,i);
        if i % 2 != 0
        {
            r := r * c;
            i := i - 1;
        }
        c := c * c;
        i := i / 2;
    }
}

lemma PotLema(a:nat, b:nat)
  ensures b % 2 == 0 ==> Pot(a,b) == Pot(a*a,b/2)
  ensures b % 2 != 0 ==> Pot(a,b) == a * Pot(a*a,(b-1)/2)
{
    if b % 2 == 0 && b > 0
    {
        PotLema(a,b-2);
    }
    if b % 2 != 0 && b > 1
    {
        PotLema(a,b-2);
    }
}