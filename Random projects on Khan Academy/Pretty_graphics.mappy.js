var domain = [-10, 10];
var numberofarrows = 200;
translate(-domain[0]/(domain[1]-domain[0])*400, 0);

var f = function(n){
    //return exp(n);                                     //no idea
    //return pow(pow(domain[1], 2) - pow(n, 2), 1/2);    //hyperbola? maybe some trig/expo
    //return 1 - pow(n, 2);                              //table bike
    //return 1/n;                                        //circle/ellipse
    return n + 1/n;                                      //parabola
    //return 1/pow(n, 2);                                //earlobe
    //return n - pow(n, 3);                              //also wormhole
    //return n - pow(n,3)/6 - 1/pow(n, 2);               //wormhole!
};

stroke(255, 0, 0);
line(-99999, 150, 99999, 150);
line(-99999, 250, 99999, 250);
stroke (0, 0, 0);

for (var x = domain[0]; x <= domain[1]; x = x + (domain[1] - domain[0])/(numberofarrows - 1)){
    line(400/(domain[1] - domain[0])*x, 150, 400/(domain[1] - domain[0])*f(x), 250);
}