/**PRESS THE RESTART BUTTON SEVERAL TIMES**/

var wood = function(){
    var array = [];
    var ext = [10, 10, 10];
    var initcolor = [random(50, 150), random(50, 150), random(50, 150)];
    //var initcolor = [92, 37, 5];
    
    array[0] = [];
    array[1] = [];
    for (var k = 1; k <= 400; k++){
        array[1][k] = [];
        array[1][k] = initcolor;
        initcolor[0] = initcolor[0] + ext[0]*random(-1, 1);
        initcolor[1] = initcolor[1] + ext[1]*random(-1, 1);
        initcolor[2] = initcolor[2] + ext[2]*random(-1, 1);
    }
    
    for(var i = 2; i <= 400; i++){
        array[i] = [];
        for (var j = 1; j <= 400; j++){
            array[i][j] = [];
            array[i][j][0] = array[i - 1][j][0] + ext[0]*random(-1, 1);
            array[i][j][1] = array[i - 1][j][1] + ext[1]*random(-1, 1);
            array[i][j][2] = array[i - 1][j][2] + ext[2]*random(-1, 1);
        }
    }
    
    for (var x = 1; x <= 400; x++){
        for (var y = 1; y <= 400; y++){
            stroke(array[x][y][0], array[x][y][1], array[x][y][2]);
            point(x, y);
        }
    }
};
var steel = function(){
    var initcolor = [random(50, 150), random(50, 150), random(50, 150)];
    var ext = 15;
    var array = [];
    for(var i = 0; i < 601; i++){
        array[i] = [];
        for(var j = 0; j < 601; j++){
            array[i][j] = [];
        }
    }
    array[0][0] = initcolor;
    for (var n = 1; n < 601; n++){
        array[0][n][0] = array[0][n-1][0] + ext*random(-1, 1);
        array[0][n][1] = array[0][n-1][1] + ext*random(-1, 1);
        array[0][n][2] = array[0][n-1][2] + ext*random(-1, 1);
    }
    for (var m = 1; m < 601; m++){
        array[m][0][0] = array[m-1][0][0] + ext*random(-1, 1);
        array[m][0][1] = array[m-1][0][1] + ext*random(-1, 1);
        array[m][0][2] = array[m-1][0][2] + ext*random(-1, 1);
    }
    
    for (var p = 1; p < 601; p++){
        for (var q = 1; q < 601; q++){
            array[p][q][0] = (array[p-1][q][0]+ext*random(-1, 1)+array[p][q-1][0]+ext*random(-1, 1))/2;
            array[p][q][1] = (array[p-1][q][1]+ext*random(-1, 1)+array[p][q-1][1]+ext*random(-1, 1))/2;
            array[p][q][2] = (array[p-1][q][2]+ext*random(-1, 1)+array[p][q-1][2]+ext*random(-1, 1))/2;
        }
    }
    for (var x = 0; x < 601; x++){
        for (var y = 0; y < 601; y++){
            stroke(array[x][y][0], array[x][y][1], array[x][y][2]);
            point(x, y);
        }
    }
};
var holomorph = function(){
    var initcolor = [random(0, 50), random(50, 150), random(50, 150)];
    var numders = 2;                  /*PLAY WITH THIS -- try 1*/
    var brightness = [800, 800, 800]; /*AND THIS -- try 400*/
    
    var ext = [brightness[0]*pow(10, -2*numders), brightness[1]*pow(10, -2*numders), brightness[2]*pow(10, -2*numders)];
    var array = [];
    for(var i = 0; i < 601; i++){
        array[i] = [];
        for(var j = 0; j < 601; j++){
            array[i][j] = [];
            for(var k = 0; k <= numders; k++){
                array[i][j][k] = [];
            }
        }
    }
    for(var o = 0; o <= numders; o++){
        if(o === 0){array[0][0][o] = initcolor;}
        if(o !== 0){array[0][0][o] = [0, 0, 0];}
    }
    for (var n = 1; n < 601; n++){
        array[0][n][numders] = [ext[0]*random(-1, 1), ext[1]*random(-1, 1), ext[2]*random(-1, 1)];
        for (var u = 1; u <= numders; u++){
            array[0][n][numders - u] = [
                array[0][n - 1][numders - u][0] + array[0][n - 1][numders - u + 1][0], 
                array[0][n - 1][numders - u][1] + array[0][n - 1][numders - u + 1][1], 
                array[0][n - 1][numders - u][2] + array[0][n - 1][numders - u + 1][2]
            ];
        }
    }
    for (var m = 1; m < 601; m++){
        array[m][0][numders] = [ext[0]*random(-1, 1), ext[1]*random(-1, 1), ext[2]*random(-1, 1)];
        for (var v = 1; v <= numders; v++){
            array[m][0][numders - v] = [
                array[m - 1][0][numders - v][0] + array[m - 1][0][numders - v + 1][0], 
                array[m - 1][0][numders - v][1] + array[m - 1][0][numders - v + 1][1], 
                array[m - 1][0][numders - v][2] + array[m - 1][0][numders - v + 1][2]
            ];
        }    
    }
    
    for (var p = 1; p < 601; p++){
        for (var q = 1; q < 601; q++){
        array[p][q][numders] = [ext[0]*random(-1, 1), ext[1]*random(-1, 1), ext[2]*random(-1, 1)];
        for (var t = 1; t <= numders; t++){
            array[p][q][numders - t] = [
                
                (array[p-1][q][numders -t][0] +
                array[p-1][q][numders - t + 1][0] +
                array[p][q-1][numders - t][0] + 
                array[p][q-1][numders - t + 1][0])/2, 
                
                (array[p-1][q][numders - t][1] + 
                array[p-1][q][numders - t + 1][1] +
                array[p][q-1][numders - t][1] + 
                array[p][q-1][numders - t + 1][1])/2, 
                
                (array[p-1][q][numders - t][2] + 
                array[p-1][q][numders - t + 1][2]+
                array[p][q-1][numders - t][2]+ 
                array[p][q-1][numders - t + 1][2])/2
                
                ];
        }
        }
    }
    for (var x = 0; x < 601; x++){
        for (var y = 0; y < 601; y++){
            stroke(array[x][y][0][0], array[x][y][0][1], array[x][y][0][2]);
            point(x, y);
        }
    }
};
var taylorsilver = function(){
    var numders = 4;
    var ext = 50;
    var derivatives = [];
    var product, sum, tempsum, val;
    for (var i = 0; i <= numders; i++){
        derivatives[i] = [];
        for(var j = 0; j <= i; j++){
            derivatives[i][j] = random(-ext, ext);
        }
    }
    var factorial = function(n){
        product = 1;
        for (var k = 1; k <= n; k++){
            product *= k;
        }
        return product;
    };
    var f = function(x, y){
        sum = 0;
        for (var m = 0; m <= numders; m++){
            tempsum = 0;
            for (var n = 0; n <= m; n++){
                tempsum += tempsum + derivatives[m][n]*pow(x, m - n)*pow(y, n)/(factorial(m - n)*factorial(n));
            }
            sum += tempsum;
        }
        return sum;
    };
    for (var a = 0; a <= 400; a++){
        for (var b = 0; b <= 400; b++){
            stroke(f(a, b));
            point(a, b);
        }
    }
};
var taylor = function(){
    var numders = 4;
    var ext = 1000;
    var derivatives = [];
    var product, sum, tempsum, val;
    for (var i = 0; i <= numders; i++){
        derivatives[i] = [];
        for(var j = 0; j <= i; j++){
            derivatives[i][j] = [random(-ext, ext), random(-ext, ext), random(-ext, ext)];
        }
    }
    derivatives[0][0] = [100, 150, 200];
    var factorial = function(n){
        product = 1;
        for (var k = 1; k <= n; k++){
            product *= k;
        }
        return product;
    };
    var f = function(x, y){
        sum = [0, 0, 0];
        for (var m = 0; m <= numders; m++){
            tempsum = [0, 0, 0];
            for (var n = 0; n <= m; n++){
                tempsum[0] += tempsum[0] + derivatives[m][n][0]*pow(x, m - n)*pow(y, n)/(factorial(m - n)*factorial(n));
                tempsum[1] += tempsum[1] + derivatives[m][n][1]*pow(x, m - n)*pow(y, n)/(factorial(m - n)*factorial(n));
                tempsum[2] += tempsum[2] + derivatives[m][n][2]*pow(x, m - n)*pow(y, n)/(factorial(m - n)*factorial(n));
            }
            sum[0] += tempsum[0];
            sum[1] += tempsum[1];
            sum[2] += tempsum[2];
        }
        return sum;
    };
    for (var a = 0; a <= 400; a+=2){
        for (var b = 0; b <= 400; b=b+=2){
            stroke(f(a/400, b/400)[0], f(a/400, b/400)[1], f(a/400, b/400)[2]);
            strokeWeight(2);
            point(a, b);
        }
    }
};
var d2initial = function(){
    var colours = [];
    var continuity = 4;
    var k = 1/400;
    var step = 2;
    for (var i = 0; i <= 400; i++){
        colours[i] = [];
        for (var j = 0; j <= 400; j++){
            colours[i][j] = [];
            for (var a = 0; a <= continuity; a++){
                colours[i][j][a] = [];
                for (var b = 0; b <= a; b++){
                    colours[i][j][a][b] = [];
                }
            }
        }
    }
    for (var a = 0; a <= continuity; a++){
        for (var b = 0; b <= a; b++){
            colours[0][0][a][b] = [random(-100,100),random(-100,100),random(-100,100)];
        }
    }
    colours[0][0][0][0] = [random(0,100),random(0,100),random(0,100)];
    for (var i = 1; i <= 400; i++){
        for (var b = 0; b <= continuity; b++){
            colours[i][0][continuity][b] = [random(-255,255),random(-255,255),random(-255,255)];
        }
        for (var a = 1; a <= continuity; a++){
            for (var b = 0; b <= continuity - a; b++){
                colours[i][0][continuity - a][b][0] = colours[i - 1][0][continuity - a][b][0] + k*colours[i - 1][0][continuity - a + 1][b][0];
                colours[i][0][continuity - a][b][1] = colours[i - 1][0][continuity - a][b][1] + k*colours[i - 1][0][continuity - a + 1][b][1];
                colours[i][0][continuity - a][b][2] = colours[i - 1][0][continuity - a][b][2] + k*colours[i - 1][0][continuity - a + 1][b][2];
            }
        }
    }
    for (var j = 1; j <= 400; j++){
        for (var b = 0; b <= continuity; b++){
            colours[0][j][continuity][b] = [random(-255,255),random(-255,255),random(-255,255)];
        }
        for (var a = 1; a <= continuity; a++){
            for (var b = 0; b <= continuity - a; b++){
                colours[0][j][continuity - a][b][0] = colours[0][j - 1][continuity - a][b][0] + k*colours[0][j - 1][continuity - a + 1][b][0];
                colours[0][j][continuity - a][b][1] = colours[0][j - 1][continuity - a][b][1] + k*colours[0][j - 1][continuity - a + 1][b][1];
                colours[0][j][continuity - a][b][2] = colours[0][j - 1][continuity - a][b][2] + k*colours[0][j - 1][continuity - a + 1][b][2];
            }
        }
        
    }
    
    for (var i = 1; i <= 400; i++){
        for (var j = 1; j <= 400; j++){
            for (var b = 0; b <= continuity; b++){
                colours[i][j][continuity][b] = [random(-255,255),random(-255,255),random(-255,255)];
            }
            
            for (var a = 1; a <= continuity; a++){
                for (var b = 0; b <= continuity - a; b++){
                    colours[i][j][continuity-a][b][0]=colours[i-1][j-1][continuity-a][b][0] + k*colours[i-1][j-1][continuity - a + 1][b][0] + k*colours[i-1][j-1][continuity - a + 1][b + 1][0];
                    colours[i][j][continuity-a][b][1]=colours[i-1][j-1][continuity-a][b][1] + k*colours[i-1][j-1][continuity - a + 1][b][1] + k*colours[i-1][j-1][continuity - a + 1][b + 1][1];
                    colours[i][j][continuity-a][b][2]=colours[i-1][j-1][continuity-a][b][2] + k*colours[i-1][j-1][continuity - a + 1][b][2] + k*colours[i-1][j-1][continuity - a + 1][b + 1][2];
                }
            }
        }
    }
    for (var i = 0; i <= 400; i++){
        for (var j = 0; j <= 400; j++){
            stroke(colours[i][j][0][0][0], colours[i][j][0][0][1], colours[i][j][0][0][2]);
            fill(colours[i][j][0][0][0], colours[i][j][0][0][1], colours[i][j][0][0][2]);
            point(i, j);
        }
    }
};
var d2final = function(){
    var colours = [];
    var continuity = 4;
    var k = 1/400;
    var step = 2;
    for (var i = 0; i <= 400; i++){
        colours[i] = [];
        for (var j = 0; j <= 400; j++){
            colours[i][j] = [];
            for (var a = 0; a <= continuity; a++){
                colours[i][j][a] = [];
                for (var b = 0; b <= a; b++){
                    colours[i][j][a][b] = [];
                }
            }
        }
    }
    for (var a = 0; a <= continuity; a++){
        for (var b = 0; b <= a; b++){
            colours[0][0][a][b] = [random(-100,100),random(-100,100),random(-100,100)];
        }
    }
    colours[0][0][0][0] = [random(0,100),random(0,100),random(0,100)];
    for (var i = 1; i <= 400; i++){
        for (var b = 0; b <= continuity; b++){
            colours[i][0][continuity][b] = [random(-255,255),random(-255,255),random(-255,255)];
        }
        for (var a = 1; a <= continuity; a++){
            for (var b = 0; b <= continuity - a; b++){
                colours[i][0][continuity - a][b][0] = colours[i - 1][0][continuity - a][b][0] + k*colours[i - 1][0][continuity - a + 1][b][0];
                colours[i][0][continuity - a][b][1] = colours[i - 1][0][continuity - a][b][1] + k*colours[i - 1][0][continuity - a + 1][b][1];
                colours[i][0][continuity - a][b][2] = colours[i - 1][0][continuity - a][b][2] + k*colours[i - 1][0][continuity - a + 1][b][2];
            }
        }
    }
    for (var j = 1; j <= 400; j++){
        for (var b = 0; b <= continuity; b++){
            colours[0][j][continuity][b] = [random(-255,255),random(-255,255),random(-255,255)];
        }
        for (var a = 1; a <= continuity; a++){
            for (var b = 0; b <= continuity - a; b++){
                colours[0][j][continuity - a][b][0] = colours[0][j - 1][continuity - a][b][0] + k*colours[0][j - 1][continuity - a + 1][b][0];
                colours[0][j][continuity - a][b][1] = colours[0][j - 1][continuity - a][b][1] + k*colours[0][j - 1][continuity - a + 1][b][1];
                colours[0][j][continuity - a][b][2] = colours[0][j - 1][continuity - a][b][2] + k*colours[0][j - 1][continuity - a + 1][b][2];
            }
        }
        
    }
    
    for (var i = 1; i <= 400; i++){
        for (var j = 1; j <= 400; j++){
            for (var b = 0; b <= continuity; b++){
                colours[i][j][continuity][b] = [random(-255,255),random(-255,255),random(-255,255)];
            }
            
            for (var a = 1; a <= continuity; a++){
                for (var b = 0; b <= continuity - a; b++){
                    colours[i][j][continuity-a][b][0]=0.5*colours[i][j-1][continuity-a][b][0] + 0.5*colours[i - 1][j][continuity-a][b][0] + k/2*colours[i-1][j][continuity - a + 1][b][0] + k*colours[i][j-1][continuity - a + 1][b + 1][0];
                    colours[i][j][continuity-a][b][1]=0.5*colours[i][j-1][continuity-a][b][1] + 0.5*colours[i - 1][j][continuity-a][b][1] + k/2*colours[i-1][j][continuity - a + 1][b][1] + k*colours[i][j-1][continuity - a + 1][b + 1][1];
                    colours[i][j][continuity-a][b][2]=0.5*colours[i][j-1][continuity-a][b][2] + 0.5*colours[i - 1][j][continuity-a][b][2] + k/2*colours[i-1][j][continuity - a + 1][b][2] + k*colours[i][j-1][continuity - a + 1][b + 1][2];

                }
            }
        }
    }
    for (var i = 0; i <= 400; i++){
        for (var j = 0; j <= 400; j++){
            stroke(colours[i][j][0][0][0], colours[i][j][0][0][1], colours[i][j][0][0][2]);
            fill(colours[i][j][0][0][0], colours[i][j][0][0][1], colours[i][j][0][0][2]);
            point(i, j);
        }
    }
};
//wood();
//steel();
//holomorph();
//taylorsilver();
//taylor();
//d2initial();
d2final();
