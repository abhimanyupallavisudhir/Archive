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
wood();