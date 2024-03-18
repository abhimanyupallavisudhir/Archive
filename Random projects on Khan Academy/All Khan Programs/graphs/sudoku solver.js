/**CLICK OUTPUT PANEL TO START SOLVING**/
var shownotes = true; //TOGGLE THIS TO SEE THE PROGRAM DOING THE WORK
var speed = 60000;    //SET THIS TO 1 FOR "FRAME-BY-FRAME" MODE -- don't set to 0.

var game = [//CHANGE THIS FOR NEW GAME
    
    [2, 0, 0,   0, 1, 0,   0, 0, 5],
    [0, 0, 1,   6, 8, 0,   0, 0, 0],
    [0, 0, 5,   0, 3, 4,   0, 0, 6],
    
    [0, 4, 0,   8, 0, 2,   5, 0, 0],
    [6, 8, 0,   0, 0, 3,   0, 2, 0],
    [3, 0, 2,   7, 0, 0,   0, 0, 0],
    
    [9, 0, 0,   5, 2, 0,   6, 0, 0],
    [0, 1, 0,   0, 7, 6,   9, 0, 0],
    [5, 0, 0,   0, 9, 0,   0, 7, 8]

    ]; //aesthetically pleasing format -- replaced by usable format later in code

var originals = [
    
    [0, 0, 0,   0, 0, 0,   0, 0, 0],
    [0, 0, 0,   0, 0, 0,   0, 0, 0],
    [0, 0, 0,   0, 0, 0,   0, 0, 0],
    
    [0, 0, 0,   0, 0, 0,   0, 0, 0],
    [0, 0, 0,   0, 0, 0,   0, 0, 0],
    [0, 0, 0,   0, 0, 0,   0, 0, 0],
    
    [0, 0, 0,   0, 0, 0,   0, 0, 0],
    [0, 0, 0,   0, 0, 6,   0, 0, 0],
    [0, 0, 0,   0, 0, 0,   0, 0, 0]

    ]; 

var digitsreverse, digits, arrmirror, arrtemp, cantbearr, cantbearr_temp, cantbecurr, cantbeuse, cantbe_tempnew, cantbe_new;
var numcells, numopts;
var paused = 0;
var p = 0, q = 0;
cantbeuse = [undefined, 1, 1, 1, 1, 1, 1, 1, 1, 1];

for (var i = 0; i < 9; i++){
    for (var j = 0; j < 9; j++){
        if(game[i][j] === 0){game[i][j] = [1, 2, 3, 4, 5, 6, 7, 8, 9];}
        else{game[i][j] = [game[i][j]]; originals[i][j] = 1;}
    }
} //rewrite game array in intellectually honest format

var arraydelete = function(arr, ind){
    arrtemp = [];
    arrtemp = arr;
    for (var n = ind; n < arr.length - 1; n++){
        arrtemp[n] = arrtemp[n+1];
    }
    arrtemp = shorten(arrtemp);
    return arrtemp;
};
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
    for (var d = digitsreverse.length; d < 9; d++){
        digitsreverse[d] = 0;
    }
    digits = mirrorarray(digitsreverse);
    return digits;
};
var index = function(num, k){
    return [3*ceil((num+1)/3)+ceil((k+1)/3)-3-1, 3*(num+1) + (k+1) - 9*ceil((num+1)/3) - 3*ceil((k+1)/3) + 9-1];
}; //index 3 by 3 squares
var findsquare = function(i, j){
    return [3*(ceil((i+1)/3)-1)+ceil((j+1)/3) - 1, 3*((i+1)-3*(ceil((i+1)/3)-1))-3+(j+1)-3*(ceil((j+1)/3)-1)-1];
};

var cantbecell = function(row, col){
    cantbearr = [];
    cantbe_new = [undefined, 1, 1, 1, 1, 1, 1, 1, 1, 1]; 
    cantbeuse = [undefined, 1, 1, 1, 1, 1, 1, 1, 1, 1];
    //column
    for (var a = 0; a < 512; a++){
        numcells = 0;
        numopts = 0;
        cantbearr_temp = [];
        cantbe_tempnew = [undefined, 1, 1, 1, 1, 1, 1, 1, 1, 1];
        if (listdigitsinbase(a, 2)[row] !== 1){
            for (var i = 0; i < 9; i++){
                if (listdigitsinbase(a, 2)[i] === 1){
                    numcells += 1;
                    for (var w = 0; w < game[i][col].length; w++){
                        cantbe_tempnew[game[i][col][w]] = 0;
                    }
                    cantbearr_temp = concat(cantbearr_temp, game[i][col]);
                }
            }
            for (var m = 1; m <= 9; m++){
                if(cantbe_tempnew[m] === 0){
                    numopts += 1;
                }
            }
            if (numcells === numopts){
                cantbearr = concat(cantbearr, cantbearr_temp);
                for (var ma = 1; ma <= 9; ma++){
                    if(cantbe_tempnew[m] === 0){
                        cantbe_new[m] = 0;
                    }
                }
            }
        }
    }
    //row
    for (var a = 0; a < 512; a++){
        numcells = 0;
        numopts = 0;
        cantbearr_temp = [];
        cantbe_tempnew = [undefined, 1, 1, 1, 1, 1, 1, 1, 1, 1];
        if (listdigitsinbase(a, 2)[col] !== 1){
            for (var j = 0; j < 9; j++){
                if (listdigitsinbase(a, 2)[j] === 1){
                    numcells += 1;
                    for (var w = 0; w < game[row][j].length; w++){
                        cantbe_tempnew[game[row][j][w]] = 0;
                    }
                    cantbearr_temp = concat(cantbearr_temp, game[row][j]);
                }
            }
            for (var m = 1; m <= 9; m++){
                if(cantbe_tempnew[m] === 0){
                    numopts += 1;
                }
            }
            if (numcells === numopts){
                cantbearr = concat(cantbearr, cantbearr_temp);
                for (var ma = 1; ma <= 9; ma++){
                    if(cantbe_tempnew[m] === 0){
                        cantbe_new[m] = 0;
                    }
                }
            }
        }
    }
    //3 by 3
    for (var a = 0; a < 512; a++){
        numcells = 0;
        numopts = 0;
        cantbearr_temp = [];
        cantbe_tempnew = [undefined, 1, 1, 1, 1, 1, 1, 1, 1, 1];
        if (listdigitsinbase(a, 2)[findsquare(row, col)[1]] !== 1){
            for (var k = 0; k < 9; k++){
                if (listdigitsinbase(a, 2)[k] === 1){
                    numcells += 1;
                    for (var w = 0; w < game[index(findsquare(row, col)[0], k)[0]][index(findsquare(row, col)[0], k)[1]].length; w++){
                        cantbe_tempnew[game[index(findsquare(row, col)[0], k)[0]][index(findsquare(row, col)[0], k)[1]][w]] = 0;
                    }
                    cantbearr_temp = concat(cantbearr_temp, game[index(findsquare(row, col)[0], k)[0]][index(findsquare(row, col)[0], k)[1]]);
                }
            }
            for (var m = 1; m <= 9; m++){
                if(cantbe_tempnew[m] === 0){
                    numopts += 1;
                }
            }
            if (numcells === numopts){
                cantbearr = concat(cantbearr, cantbearr_temp);
                for (var ma = 1; ma <= 9; ma++){
                    if(cantbe_tempnew[m] === 0){
                        cantbe_new[m] = 0;
                    }
                }
            }
        }
    }

    for (var l = 0; l < cantbearr.length; l++){
        cantbeuse[cantbearr[l]] = 0;
    }
    return cantbeuse;
};
var solvecell = function(i, j){
    cantbecurr = [];
    cantbecurr = cantbecell(i, j);
    for (var t = 0; t < game[i][j].length; t++){
        if (cantbecurr[game[i][j][t]] === 0){
            game[i][j] = arraydelete(game[i][j], t);
            t-=1;
        }
    }
};

var draw = function() {
    background(255);
    strokeWeight(2);
    fill(255, 255, 255, 0);
    stroke(0);
    for (var xc = 0; xc < 3; xc++){
        for (var yc = 0; yc < 3; yc++){
            rect(20+120*xc, 20+120*yc, 120, 120);
        }
    }
    strokeWeight(1);
    for (var xc = 0; xc < 9; xc++){
        for (var yc = 0; yc < 9; yc++){
            rect(20+40*xc, 20+40*yc, 40, 40);
            if (originals[yc][xc] === 1){fill(0, 0, 0);}
            else {fill(0, 0, 180);}
            if(game[yc][xc].length === 1){
                textSize(20);
                text(game[yc][xc], 13+20+40*xc, 27+20+40*yc);
            }
            else if (shownotes === true){
                textSize(10);
                fill(150, 150, 150);
                for (var v = 0; v < game[yc][xc].length; v++){
                    if(game[yc][xc][v] === 1){text("1", 5+20+40*xc, 15+20+40*yc);}
                    if(game[yc][xc][v] === 2){text("2", 15+20+40*xc, 15+20+40*yc);}
                    if(game[yc][xc][v] === 3){text("3", 25+20+40*xc, 15+20+40*yc);}
                    if(game[yc][xc][v] === 4){text("4", 5+20+40*xc, 25+20+40*yc);}
                    if(game[yc][xc][v] === 5){text("5", 15+20+40*xc, 25+20+40*yc);}
                    if(game[yc][xc][v] === 6){text("6", 25+20+40*xc, 25+20+40*yc);}
                    if(game[yc][xc][v] === 7){text("7", 5+20+40*xc, 35+20+40*yc);}
                    if(game[yc][xc][v] === 8){text("8", 15+20+40*xc, 35+20+40*yc);}
                    if(game[yc][xc][v] === 9){text("9", 25+20+40*xc, 35+20+40*yc);}
                }
            }
            fill(255, 255, 255, 0);
        }
    }
    
    solvecell(p, q);
    mouseClicked = function(){
        paused ++;
    };
    if (paused % 2 === 1){
        if (q < 9){
            q++;
        }
        if (q === 9){
            if (p < 8){
                p++;
                q=0;
            }
        }
        if (q === 8){
            if (p === 8){
                q = 0;
                p = 0;
            }
        }
    }
    fill(0, 0, 180);
    textSize(10);
    text ("Click to start/pause solving", 260, 15);
    if (paused % 2 === 0){
        fill(0, 140, 0);
        text("PAUSED", 180, 15);
    }
    if (paused % 2 === 1){
        fill(180, 0, 0);
        text("SOLVING", 178, 15);
    }
    frameRate(speed);
};

/*var cantbe = function(type, num){
    cantbearr = [];
    //type = 1: column
    //type = 2: row
    //type = 3: 3 by 3 square
    if (type === 1){
        for (var a = 0; a < 512; a++){
            numcells = 0;
            numopts = 0;
            cantbearr_temp = [];
            for (var i = 0; i < 9; i++){
                if (listdigitsinbase(a, 2)[i] === 1){
                    numcells += 1;
                    numopts += game[i][num].length;
                    cantbearr_temp = concat(cantbearr_temp, game[i][num]);
                }
            }
            if (numcells === numopts){
                cantbearr = concat(cantbearr, cantbearr_temp);
            }
        }
    }
    if (type === 2){
        for (var a = 0; a < 512; a++){
            numcells = 0;
            numopts = 0;
            cantbearr_temp = [];
            for (var j = 0; j < 9; j++){
                if (listdigitsinbase(a, 2)[j] === 1){
                    numcells += 1;
                    numopts += game[num][j].length;
                    cantbearr_temp = concat(cantbearr_temp, game[num][j]);
                }
            }
            if (numcells === numopts){
                cantbearr = concat(cantbearr, cantbearr_temp);
            }
        }
    }
    if (type === 3){
        for (var a = 0; a < 512; a++){
            numcells = 0;
            numopts = 0;
            cantbearr_temp = [];
            for (var k = 0; k < 9; k++){
                if (listdigitsinbase(a, 2)[k] === 1){
                    numcells += 1;
                    numopts += game[index(num, k)[0]][index(num, k)[1]].length;
                    cantbearr_temp = concat(cantbearr_temp, game[index(num, k)[0]][index(num, k)[1]]);
                }
            }
            if (numcells === numopts){
                cantbearr = concat(cantbearr, cantbearr_temp);
            }
        }
    }
    return cantbearr;
};*/