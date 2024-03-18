/**INITIALISE -- variables, basic functions, initialising loops**/
var tmax = 100;                  //CHANGE IF TOO SLOW
var numbiomes = 100;             //CHANGE IF TOO SLOW
var initpop = 100;               //CHANGE IF TOO SLOW
var initlifespan = 5; 
var initreproprob = 0.2;
var mutationprob = 0.01;
var mutationstrength = 0.01;
var initbiomecap = 1000;
var randrepro, randmutate;
var initpops = []; 
var biomecaps = [];
var creatures = [];
var creature = function(biome, individual, age, lifespan, reproprob){
    this.biome = biome;
    this.individual = individual;
    this.age = age;
    this.lifespan = lifespan;
    this.reproprob = reproprob;
    return [this.biome, this.individual, this.age, this.lifespan, this.reproprob];
};
for (var k = 0; k < numbiomes; k++){initpops[k] = initpop;}
for (var l = 0; l < numbiomes; l++){biomecaps[l] = initbiomecap;}
for (var i = 0; i < numbiomes; i++){
    creatures[i] = [];
    for (var j = 0; j < initpops[i]; j++){
        creatures[i][j] = creature(i, j, 0, initlifespan, initreproprob);
    }
}
var neighbour = function(biome){
    if(biome === 0){return creatures.length - 1;}
    if(biome !== 0){return biome - 1;}
};

/**LIFE FUNCTIONS**/
var reproduce = function(biome, individual){
    randmutate = random(0, 1);
    this.b = biome;
    this.i = creatures[biome].length;
    this.a = 0;
    this.l = creatures[biome][individual][3];
    this.r = creatures[biome][individual][3];
    if (randmutate < mutationprob/2){this.r = this.r + mutationstrength;}
    if (randmutate > 1 - mutationprob/2){this.r = this.r - mutationstrength;}
    creatures[this.b][this.i] = creature(this.b, this.i, this.a, this.l, this.r);
};
var grow = function(biome, individual){
    creatures[biome][individual][2] = creatures[biome][individual][2] + 1;
};
var die = function(biome, individual){
    for (var o = individual; o < creatures[biome].length - 1; o++){
        creatures[biome][o] = creatures[biome][o + 1];
    }
    creatures[biome].pop();
};
var extinction = function(biome, invadingbiome){
    for (var m = 0; m < creatures[biome].length; m++){
        creatures[biome].pop();
    }
    for (var n = 0; n < creatures[invadingbiome].length; n++){
        creatures[biome][n] = creatures[invadingbiome][n];
        creatures[biome][n][2] = 0;
    }
};

/**RUN EVOLUTION**/
for (var t = 1; t < tmax; t++){
    for (var p = 0; p < numbiomes; p++){
        for(var q = 0; q < creatures[p].length; q++){
            randrepro = random(0, 1);
            if(randrepro < creatures[p][q][4]){
                reproduce(p, q);
            }
            if(creatures[p][q][2] >= creatures[p][q][3]){
                die(p, q);
            }
            grow(p, q);
        }
        if (creatures[p].length > biomecaps[p]){
            extinction(p, neighbour(p));
        }
    }
}

/**PROVIDE OUTPUT**/
var population = 0;
var avgreprorate = 0;

for (var x = 0; x < creatures.length; x++){
    population = population + creatures[x].length;
    for (var y = 0; y < creatures[x].length; y++){
        avgreprorate = avgreprorate + creatures[x][y][3]*creatures[x][y][4];
    }
}

avgreprorate = avgreprorate/population;

println("Population:" + population);
println("Average reproduction rate:" + avgreprorate);

/**DEBUGGING**/
println("Debugging:");