/**SOMETHING WEIRD HAPPENS AFTER the power reaches 153.**/

/*INSPIRED BY MATHOLOGER's video: "Times Tables, Mandelbrot and the Heart of Mathematics"*/
/*(Try 30 and 300, 30 and 400), 40 and 300 -- you'll have to remove the draw loop*/

var animspeed = 0.05;
var tableOf = 0;
var smoothness = 100;
var power = 0;          /*---------------------SET THIS TO 153.-------------------------*/
var product;

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

var takepower = function(base, exponent){
    product = 1;
    for(var multid = 0; multid < exponent; multid++){
        product = product*base;
    }
    return product;
};

var connection = function(entryID){
    entry(entryID);
    this.posX1 = posX;
    this.posY1 = posY;
    entry(takepower(entryID, power));
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
    fill(0, 0, 0);
    text(power, 300, 300);
    power = power + animspeed;
};
