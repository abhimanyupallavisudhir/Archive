/**FIND THE CORRELATION BETWEEN NUMBERS AND THEIR MIRROR NUMBERS (e.g. 1846 and 6481)**/

/*var fastcount = true; //turn off to use with large uppercaps and for live graphing*/
/*var screencapinslowcount = 1000;*/
var uppercap = 200000;
var base = 10;

var sx = 0, sy = 0, sx2 = 0, sy2 = 0, sxy = 0;
var ex = 0, ey = 0, ex2 = 0, ey2 = 0, exy = 0;
var corr;

var startpagescroll = false;
var arrmirror, digitsreverse, digits, inv_digits, curr, x_curr, y_curr, plot_curr, plot_corr;
var nums = [];

//FUNCTIONS NECESSARY TO DEFINE MIRRORNUM(NUM)
var mirrorarray = function(digs){
    arrmirror = [];
    for (var i = 0; i <= digs.length - 1; i++){
        arrmirror[i] = digs[digs.length - 1 - i];
    }
    return arrmirror;
};
var listdigitsinbase = function(num, b){
    digitsreverse = [];
    digits = [];
    while (num > 0){
        digitsreverse[digitsreverse.length] = num % b;
        num = (num - num % b)/b;
    }
    digits = mirrorarray(digitsreverse);
    return digits;
};
var inv_listdigitsinbase = function(digs, b){
    inv_digits = 0;
    for (var d = 0; d <= digs.length - 1; d+=1){
        inv_digits += digs[d]*pow(b, digs.length - 1 - d);
    }
    return inv_digits;
};
var mirrornum = function(num){
    return inv_listdigitsinbase(mirrorarray(listdigitsinbase(num, base)), base);
};

//TRY PLAYING WITH DIFFERENT FUNCTIONS INSTEAD OF MIRRORNUM
var f = function(num){return mirrornum(num);};

/*if (fastcount === true){*/
    for (curr = 0; curr <= uppercap; curr++){
        x_curr = curr;
        y_curr = f(curr);
        sx += x_curr;
        sy += y_curr;
        sx2 += pow(x_curr, 2);
        sy2 += pow(y_curr, 2);
        sxy += x_curr*y_curr;
        ex = sx/(curr + 1);
        ey = sy/(curr + 1);
        ex2 = sx2/(curr + 1);
        ey2 = sy2/(curr + 1);
        exy = sxy/(curr + 1);
        corr = (exy - ex*ey)/pow((ex2 - pow(ex, 2))*(ey2 - pow(ey, 2)), 1/2);
        
        //DRAW
        plot_curr = curr/uppercap*400;
        plot_corr = 200 - 200*corr;
        point(plot_curr, plot_corr);
    }
    println(corr);
/*}*/
/*if (fastcount === false){
    curr = 0;
    var draw = function() {
        curr = curr + 1;
        x_curr = curr;
        y_curr = f(curr);
        sx += x_curr;
        sy += y_curr;
        sx2 += pow(x_curr, 2);
        sy2 += pow(y_curr, 2);
        sxy += x_curr*y_curr;
        ex = sx/(curr + 1);
        ey = sy/(curr + 1);
        ex2 = sx2/(curr + 1);
        ey2 = sy2/(curr + 1);
        exy = sxy/(curr + 1);
        corr = (exy - ex*ey)/pow((ex2 - pow(ex, 2))*(ey2 - pow(ey, 2)), 1/2);
        
        //DRAW
        if (startpagescroll === false){
            plot_curr = curr/screencapinslowcount*400;
            if (plot_curr >= 400){
                startpagescroll = true;
            }
        }
        if (startpagescroll === true){
            translate(-curr*screencapinslowcount/400, 0);
            plot_curr = 400;
        }
        plot_corr = 200-200*corr;
        point(plot_curr, plot_corr);
        frameRate(99999999);
    };
}*/