var t = 0;
var xcoord = 300;
var ycoord = 300;
var xSpeed, ySpeed, speed;
var headX;
var headY;

var draw = function() {
    //Plot head
    stroke(0, 0, 0);
    headX = 200 + 100*cos(t);
    headY = 200 + 100*sin(t);
    point(headX, headY);
    //Plot tail
    stroke(255, 0, 0);
    xSpeed = headX - xcoord;
    ySpeed = headY - ycoord;
    speed = sqrt(xSpeed*xSpeed + ySpeed*ySpeed);
    xSpeed = xSpeed/speed;
    ySpeed = ySpeed/speed;
    xcoord = xcoord + xSpeed;
    ycoord = ycoord + ySpeed;
    point(xcoord, ycoord);
    t = t + 1;
};