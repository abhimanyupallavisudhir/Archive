/**The correct formula (confirmed by this sim) is the following: prob = 7^(2-sqside)**/

var sqside = 3; //CHANGE THIS

var state; 
var tstate;
var centralsquare;
var randnum;
var cheese = 0; 
var deadmouse = 0;
var fedmouse = 0; 
var endmouse; 
var prob; 

for(var s = 0; s < sqside - 1; s++){
    rect(50 + s*300/sqside, 50, 300/sqside, 300/sqside);
    rect(350 - 300/sqside, 50 + s*300/sqside, 300/sqside, 300/sqside);
    rect(350 - 300/sqside - s*300/sqside, 350 - 300/sqside, 300/sqside, 300/sqside);
    rect(50, 350 - 300/sqside - s*300/sqside, 300/sqside, 300/sqside);
}
fill(145, 145, 145);
rect(50 + 300/sqside, 50 + 300/sqside, 300 - 2*300/sqside, 300 - 2*300/sqside);

for(var t = 1; t <= 1000000; t++){
    state = 1;
    endmouse = 0;
    cheese = 0;
    while (endmouse === 0){
        centralsquare = 0;
        randnum = random(0,1);
        if(state%(sqside - 1) === 0){
            if(randnum < 1/2){tstate = (state + 1)%(4*sqside - 4);}
            if(randnum > 1/2){tstate = (state + (4*sqside - 5))%(4*sqside - 4);}
        }
        else{
            if(randnum < 1/3){tstate = (state + 1)%(4*sqside - 4);}
            else if(randnum > 2/3){tstate = (state + (4*sqside - 5))%(4*sqside - 4);}
            else{centralsquare = 1;}
        }
        if(state === 2*(sqside - 1)){cheese = 1;}
        if(centralsquare === 1){
            if (cheese === 0){deadmouse = deadmouse + 1;}
            if (cheese === 1){fedmouse = fedmouse + 1;}
            endmouse = 1;
        }
        state = tstate;
    }
}

prob = fedmouse/(fedmouse + deadmouse);
println("probability of mouse fed before dead: "+prob);