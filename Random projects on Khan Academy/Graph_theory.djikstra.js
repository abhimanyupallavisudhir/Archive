var vertexA = 1; 
var vertexB = 18;

var currentvertex = vertexA; 
var openvertices = []; 
var graph = [[0,2,9,6,5,7,5,9,8,0,5,5,0,0,6,6,8,3,1,3],
             [2,0,3,0,2,1,0,0,1,3,6,2,6,9,4,9,6,0,8,3],
             [9,3,0,9,9,4,1,2,5,5,5,4,6,5,1,8,8,7,5,3],
             [6,0,9,0,7,7,7,8,4,4,2,2,8,4,4,5,5,1,7,1],
             [5,2,9,7,0,4,5,5,1,9,9,1,5,5,5,5,2,1,9,7],
             [7,1,4,7,4,0,7,8,7,9,8,0,1,2,9,3,5,1,1,3],
             [5,0,1,7,5,7,0,6,0,6,9,4,2,6,1,3,4,5,3,4],
             [9,0,2,8,5,8,6,0,1,4,9,0,0,5,9,0,9,0,4,3],
             [8,1,5,4,1,7,0,1,0,4,9,1,4,9,9,9,7,9,0,1],
             [0,3,5,4,9,9,6,4,4,0,8,4,0,8,5,4,1,3,8,9],
             [5,6,5,2,9,8,9,9,9,8,0,4,8,9,3,1,9,0,3,8],
             [5,2,4,2,1,0,4,0,1,4,4,0,1,7,2,1,9,5,1,0],
             [0,6,6,8,5,1,2,0,4,0,8,1,0,5,2,2,4,0,0,9],
             [0,9,5,4,5,2,6,5,9,8,9,7,5,0,9,4,2,1,8,6],
             [6,4,1,4,5,9,1,9,9,5,3,2,2,9,0,9,3,0,4,0],
             [6,9,8,5,5,3,3,0,9,4,1,1,2,4,9,0,8,8,5,6],
             [8,6,8,5,2,5,4,9,7,1,9,9,4,2,3,8,0,9,4,6],
             [3,0,7,1,1,1,5,0,9,3,0,5,0,1,0,8,9,0,2,6],
             [1,8,5,7,9,1,3,4,0,8,3,1,0,8,4,5,4,2,0,8],
             [3,3,3,1,7,3,4,3,1,9,8,0,9,6,0,6,6,6,8,0]];
var labels = [];
for (var a = 0; a < graph.length; a++){
    for (var b = 0; b < graph.length; b++){
        if(graph[a][b] === 0){graph[a][b] = Infinity;} //0 in the adj table is really infty
    }
}
for (var v = 0; v < graph.length; v++){                  
    labels[v] = [undefined, undefined, undefined, undefined, Infinity, undefined];
}
labels[vertexA] = [1, 0, undefined, 1, 0, undefined];   

var minimum = function(setofvertices){        
    this.val = setofvertices[0];
    for (var w = 0; w < setofvertices.length; w++){
        if (labels[setofvertices[w]][4] < labels[setofvertices[this.val]][4]){
            this.val = setofvertices[w];
        }
    }
    return this.val;
};
var openneighbours = function(vertexID){
    for (var x = 0; x < graph.length; x++){
        if (graph[vertexID][x] !== Infinity){
            if (labels[x][2] === undefined){
                if (labels[vertexID][1] + graph[vertexID][x] < labels[x][4]){
                    labels[x][3] = labels[vertexID][0] + 1;
                    labels[x][4] = labels[vertexID][1] + graph[vertexID][x];
                    labels[x][5] = vertexID;
                    openvertices[openvertices.length] = x;
                }
            }
        }
    }
};
var closevertex = function(vertexID){
    labels[vertexID][0] = labels[vertexID][3];
    labels[vertexID][1] = labels[vertexID][4];
    labels[vertexID][2] = labels[vertexID][5];
};

var draw = function() {
    if (labels[vertexB][2] === undefined){
        openneighbours(currentvertex);
        currentvertex = minimum(openvertices);
        closevertex(currentvertex);
    }
    println(currentvertex);
};