var m = 0;
var i = 0;
var n = 0;
var K = 1000000;

for (var k = 0; k <= K; k++){
    i = 0; m = 0;
    while (m < 1){
        m += random(0, 1);
        i += 1;
    }
    n += i/K;
}
println(n);

//why are there always so many recurring nines in the result? Weird.