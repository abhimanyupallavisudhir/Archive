/*NOTES: 600 x 600 size used*/

/**RANDOM RUN: Perform various integrals of a random walk
               * Set dorder = 0 for random function
               * Set dorder = 1 for random walk
               * For cool effect, replace line 23 with line(j - 1, xprev, xders[0], j);
*/

var dorder = 3;                        //order of differentiability/smoothness
var xders = [];                        //initial conditions
var xprev;
for (var i = 0; i <= dorder; i++){
    if(i === 0){
        xders[i] = 300;
    }
    if(i !== 0) {xders[i] = 0;}
} //set initial conditions (z-transform)

for(var j = 1; j <= 600;j=j+1/2){
    xprev = xders[0];
    xders[xders.length - 1] = random(-1, 1)*500/pow(50, dorder);
    for (var k = 1; k <= xders.length - 1; k++){
        xders[xders.length - 1 - k] = xders[xders.length - 1 - k] + xders[xders.length - k];
    }
    line(j - 1/2, xprev, j, xders[0]); 
}
