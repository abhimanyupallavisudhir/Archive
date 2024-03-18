var nested_gen = function(num){
    var input = pow (num, 1/2), runs = 100;
    var val;
    val = input;
    for (var i = runs; i >= 1; i = i - 1){
        val = pow(num + i*val, 1/2);
    }
    return val;
};
println("nested root of 6 is " + nested_gen(6));

var x = 0;
var draw = function(){
    stroke(255, 0, 0);
    line(x, 200-8*nested_gen(x), x - 1, 200-8*nested_gen(x - 1));
    stroke(0, 0, 0);
    line(x, 200-8*sqrt(x), x - 1, 200-8*sqrt(x - 1));
    stroke(0, 0, 255);
    line(x, 80-80*(nested_gen(x) - sqrt(x)), x - 1, 80-80*(nested_gen(x - 1) - sqrt(x - 1)));
    if(x < 400){x = x + 1;}
};
stroke(100, 100, 255);
line(0, 80, 400, 80);
fill(255, 0, 0);
text("nested_Gen(x)", 250, 290);
fill(0, 0, 0);
text("sqrt(x)", 250, 305);
fill (0, 0, 255);
text("Difference (in different axes)", 250, 320);

println(nested_gen(10000000)-sqrt(10000000));
