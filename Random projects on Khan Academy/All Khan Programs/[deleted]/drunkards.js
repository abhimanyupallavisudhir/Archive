var x1 = width/2;
var y1 = height/2;
var x2 = width/2;
var y2 = width/2 - 100;


var randnum;
var dir = [0, 0];

var prevmove = 3;
var move;
var movesarray = [0, 1, 2];

var drunkard1 = function(){
        point(x1, y1);
        randnum = random(0, 1);
        if(randnum < 0.25){x1 = x1 + 1;}
        if(randnum >= 0.25 & randnum < 0.50){y1 = y1 + 1;}
        if(randnum >= 0.50 & randnum < 0.75){x1 = x1 - 1;}
        if(randnum >= 0.75){y1 = y1 - 1;}
};

var drunkard2 = function(){
  point(x2, y2);
  randnum = random(0, 1);
  if(prevmove === 0){movesarray = [1, 2, 3];}
  if(prevmove === 1){movesarray = [0, 2, 3];}
  if(prevmove === 2){movesarray = [0, 1, 3];}
  if(prevmove === 3){movesarray = [0, 1, 2];}
  if(randnum < 1/3){move = movesarray[0];}
  if(randnum >= 1/3 & randnum < 2/3){move = movesarray[1];}
  if(randnum >= 2/3){move = movesarray[2];}
  if(move === 0){x2 = x2 + 1;}
  if(move === 1){y2 = y2 + 1;}
  if(move === 2){x2 = x2 - 1;}
  if(move === 3){y2 = y2 - 1;}
  prevmove = move;
};

var draw = function() {
    stroke(255, 0, 0);
    drunkard1();
    stroke(0, 0, 255);
    drunkard2();
    frameRate(60000);
};
