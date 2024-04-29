ghost predicate ordenado (s: seq<int>)
{
    forall i,j ::0 <= i < j < |s| ==> s[i] <= s[j] 
}

ghost predicate ordenadov2(s: seq<int>)
{
    if |s| <= 1  
    then true
    else ordenadov2(s[1..]) && s[0] <= s[1]  
}

// ghost predicate Permutacao (a:seq<int>, b:seq<int>)
// {
//     forall i,j:int  :: i in a && j in b 
// }

ghost predicate Permutacao (a:seq<int>, b:seq<int>)
{
    // https://dafny.org/dafny/OnlineTutorial/ValueTypes#:~:text=..i%5D-,Multisets,-Multisets%20are%20like
    multiset(a) == multiset(b)
}

method Main()
{
    var a := new int[3];
    a[0],a[1],a[2] := 1,2,3;
    var b := new int[3];
    b[0],b[1],b[2] := 3,1,2;
    assert a[..] == [1,2,3]; // solicitar prova de igualdade antes de submeter
    assert b[..] == [3,1,2]; // solicitar prova de igualdade antes de submeter
    assert Permutacao(a[..],b[..]);    
}

/*
4) Especifique, implemente e prove a correção de um método que recebe um array de números 
inteiros, e dois índices i e j e faz uma troca (swap) entre os elementos encontrados nas posições i e 
j. Não esqueça de realizar um teste unitário em um método Main para verificar se sua 
especificação é adequada. Utilize a seguinte assinatura para o método:
*/

method TrocaElementos(a: array<int>, i: int, j: int)
requires a.Length > 0 
requires j >= 0 && j < a.Length
requires i >= 0 && i < a.Length 
modifies a // permite a modificacao do parametro
ensures a[i] == old (a[j]) && a[j] == old (a[i]) // garante a troca 
ensures Permutacao(a[..], old(a[..])) // garante que os valores internos nao mudaram
ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k]) // garante que os outros elementos continuam na mesma ordem
{
    a[i], a[j] := a[j], a[i];
}

/*
5) Deseja-se implementar e verificar a correção do método de ordenação de arrays conhecido 
como BubbleSort. Os seguintes predicados já estão definidos e podem ser utilizados na verificação 
do método BubbleSort a ser implementado em Dafny. A fim de simplificar, estamos utilizando 
somente arrays de inteiros. Não esqueça de realizar um teste unitário em um método Main para 
verificar se sua especificação é adequada.
*/
ghost predicate Permutacao(a:seq<int>, b:seq<int>)
{
 multiset(a) == multiset(b)
}
ghost predicate OrdenadoEntre(a:array<int>, e:int, d:int)
 requires 0 <= e <= d <= a.Length
 reads a
{
 forall i,j ::e <= i <= j < d ==> a[i] <= a[j]
}
ghost predicate Ordenado(a:array<int>)
 reads a
{
 OrdenadoEntre(a,0,a.Length)
}

method BubbleSort (a:array<int>)
    ensures Ordenado(a)   
    ensures Permutacao(a[..], old(a[..]))
    // modifies 