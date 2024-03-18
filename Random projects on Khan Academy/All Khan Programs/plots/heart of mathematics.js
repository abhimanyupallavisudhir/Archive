/**INSPIRED BY MATHOLOGER's video: "Times Tables, Mandelbrot and the Heart of Mathematics"**/
/*(Try 30 and 300, 30 and 400), 40 and 300 -- you'll have to remove the draw loop*/

var animspeed = 0.005;
var tableOf = 0;
var smoothness = 100;

/*var remainder;
var modulus = function(posnum, base){
    remainder = posnum;
    while (remainder > base){
        remainder = posnum - base;
    }
};*/

var posX;
var posY;
var pointlessentry = function(index){
    this.id = index;
    posX = 200 + 100*cos(360*index/smoothness);
    posY = 200 + 100*sin(360*index/smoothness);
};

var entry = function(index){
    pointlessentry(index);
    point(posX, posY);
};

var connection = function(entryID){
    entry(entryID);
    this.posX1 = posX;
    this.posY1 = posY;
    entry(entryID*tableOf);
    this.posX2 = posX;
    this.posY2 = posY;
    line(this.posX1, this.posY1, this.posX2, this.posY2);
};

var draw = function() {
    background(255, 255, 255);
    for(var i = 0; i < smoothness; i++){
        entry(i);
        connection(i);
    }
    tableOf = tableOf + animspeed;
};
