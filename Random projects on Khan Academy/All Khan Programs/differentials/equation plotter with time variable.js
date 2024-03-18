var animated = 1;
var speed = 0.01;
var changingconst = "E";

var stepx = 0.01;
var xmin = -10, xmax = 10, ymin = -10, ymax = 10;
var A = 1, B = 0, C = 0, D = 0, E = 0, F = 1;      //parameters for the function

translate(200, 200);
scale(400/(xmax - xmin), -400/(ymax - ymin));
var thinline = function(x1, y1, x2, y2){
    strokeWeight((xmax - xmin)/400);
    line(x1, y1, x2, y2);
    strokeWeight(1);
};
var thinellipse = function(x, y, w, h){
    strokeWeight((xmax - xmin)/400);
    ellipse(x, y, w, h);
    strokeWeight(1);
};
var thinpoint = function(x, y){
    scale(1/(xmax - xmin), 1/(ymax - ymin));
    point(x*(xmax - xmin), y*(ymax - ymin));
    scale(xmax - xmin, ymax - ymin);
};

var draw = function() {
    background(255, 255, 255);
    thinline(xmin, 0, xmax, 0);
    thinline(0, ymin, 0, ymax);

    var f = function(x){
        return (A*x*x + B*x + C)/(D*x*x + E*x + F);
    };
    
    var plotf = function(){
        for(var x = xmin; x <= xmax; x = x + stepx){
            thinpoint(x, f(x));
            //thinline(x - stepx, f(x - stepx), x, f(x));
        }
    };
    plotf();
    if(animated === 1){
        if(changingconst === "A"){
            A = A + speed;
        }
        if(changingconst === "B"){
            B = B + speed;
        }
        if(changingconst === "C"){
            C = C + speed;
        }
        if(changingconst === "D"){
            D = D + speed;
        }
        if(changingconst === "E"){
            E = E + speed;
        }
        if(changingconst === "F"){
            F = F + speed;
        }
    }
};