method Main() {
    var i, n := 0, 11;
    while i < n
      //decreases n - i
    {
        i := i + 5;
    }
    //na última iteração do loop i=15 e n-i=-4, Dafny aceita pois o loop não executará novamente
}
