var state; //choose one: mousya pradesh or mouisiana? fine i'll give you mousesthan, the state where tom and jerr is banned. ok fine you can have mouse nadu too, where all the chief ministers are circus mice. 
var randnum; //lying shills it's not random
var cheese = 0; //haha dumb mouse
var deadmouse = 0; //that's why you should just nuke the mouse
var fedmouse = 0;  //starving mice in mathproblemica
var endmouse; //one way or the other, the mouse will come to an end today
var prob = []; //probiotic mouse. short form: potty mouse. just like potty sulfate.
var avgprob = 0;

var probcalc = function(i){
    for(var t = 1; t <= 100000; t++){
        state = 1;
        endmouse = 0;
        cheese = 0;
        while (endmouse === 0){
            if(state === 1){
                randnum = random(0,1);
                if(randnum < 1/2){state = 2;}
                if(randnum > 1/2){state = 4;}
            }
            if(state === 2){
                randnum = random(0,1);
                if(randnum < 1/3){state = 1;}
                if(randnum > 2/3){state = 3;}
                if(randnum >= 1/3 & randnum <= 2/3)  {state = 5;}
            }
            if(state === 3){
                randnum = random(0,1);
                if(randnum < 1/2){state = 2;}
                if(randnum > 1/2){state = 6;}
            }
            if(state === 4){
                randnum = random(0,1);
                if(randnum < 1/3){state = 1;}
                if(randnum > 2/3){state = 7;}
                if(randnum >= 1/3 & randnum <= 2/3) {state = 5;}
            }
            if(state === 6){
                randnum = random(0,1);
                if(randnum < 1/3){state = 3;}
                if(randnum > 2/3){state = 9;}
                if(randnum >= 1/3 & randnum <= 2/3) {state = 5;}
            }
            if(state === 7){
                randnum = random(0,1);
                if(randnum < 1/2){state = 4;}
                if(randnum > 1/2){state = 8;}
            }
            if(state === 8){
                randnum = random(0,1);
                if(randnum < 1/3){state = 7;}
                if(randnum > 2/3){state = 9;}
                if(randnum >= 1/3 & randnum <= 2/3) {state = 5;}
            }
            if(state === 9){
                cheese = 1; 
                randnum = random(0,1);
                if(randnum < 1/2){state = 6;}
                if(randnum > 1/2){state = 8;}
            }
            if(state === 5){
                if (cheese === 0){deadmouse = deadmouse + 1;}
                if (cheese === 1){fedmouse = fedmouse + 1;}
                endmouse = 1;
            }
        }
    }
    prob[i] = fedmouse/(fedmouse + deadmouse);
};

for(var i = 0; i < 100; i++){
    probcalc(i);
    avgprob = avgprob + prob[i]/100;
}

println(avgprob);