var numprices = 3;

var price = 0;
var prevprice = 0;
var fluctuation;

var c1, c2, c3;

var fineness = 0.78;

var drawprice = function(){
    c1 = random(0, 225);
    c2 = random(0, 255 - c1);
    c3 = 255 - c1 - c2;
    stroke(c1, c2, c3);
    //strokeWeight(10);                                  //to find out the colour
    for (var t = 0; t < 400/fineness; t += fineness){
        fluctuation = random(-10, 10);
        price = price + fluctuation;
        point(t, 200 + price);
        line(t, 200 + price, t - 1, 200 + prevprice);
        prevprice = price;
    }
    prevprice = 0;
    price = 0;
};

for (var graph = 0; graph < numprices; graph++){
    drawprice();
}