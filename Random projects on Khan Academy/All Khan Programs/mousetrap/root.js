var state; //choose one: mousya pradesh or mouisiana? fine i'll give you ratasthan, but remember  tom and jerr is banned there. ok fine you can have mouse nadu too but all the chief ministers are circus mice. yes, i know mousenataka's politicians are lab mice on sleeping pills crossing ld50
var randnum; //lying shills it's not random
var cheese = 0; //haha dumb mouse
var deadmouse = 0; //thats why you should just nuke the mouse
var fedmouse = 0;  //essentially why you have starving mice in africa
var endmouse; //one way or the other, the mouse will come to an end today
var prob; //probiotic mouse. short form: potty mouse. just like potty sulfate.

rect(50,50,100,100);    //mousebox  -- state = 1
rect(150,150,100,100);  //trapbox   -- state = 5
rect(250,250,100,100);  //cheesebox -- state = 9

rect(150,50,100,100);   //miscbox   -- state = 2
rect(250,50,100,100);   //miscbox   -- state = 3
rect(50,150,100,100);   //miscbox   -- state = 4
rect(250,150,100,100);  //miscbox   -- state = 6
rect(50,250,100,100);   //miscbox   -- state = 7
rect(150,250,100,100);  //miscbox   -- state = 8

for(var t = 1; t <= 1000000; t++){
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

prob = fedmouse/(fedmouse + deadmouse);
println("probability of mouse fed before dead: "+prob);