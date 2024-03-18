/**UNTRAINED, BACKPROPAGATION NOT YET ENCODED!**/

var input = 10982467;
var trainingdata = []; //List of primes
var neurons = [];
var weights = [];
var biases = [];
var layers = [1, 10, 10, 10, 10, 10, 10, 10, 10, 1];

//initialise neural network
var constructnetwork = function(){
    biases[0] =[undefined];
    weights[0] = [[undefined]]; //no weights and biases for the first layer
    for (var i = 1; i < layers.length; i++){ //start at 1 because 0th layer is input
        neurons[i] = [];
        weights[i] = [];
        biases[i] = [];
        for (var j = 0; j < layers[i]; j++){
            neurons[i][j] = undefined;
            weights[i][j]=[];
            biases[i][j] = random(-1, 1);
            for (var k = 0; k < layers[i - 1]; k++){
                weights[i][j][k] = random(-1, 1);
            }
        }
    }
};

var forwardpropagation = function(num){
    neurons[0] = [num];
    for (var p = 1; p < layers.length; p++){
        for (var q = 0; q < layers[p]; q++){
            this.val = 0;
            for (var r = 0; r < layers[p - 1]; r++){
                this.val = this.val + neurons[p - 1][r]*weights[p][q][r];
            }
            this.val = this.val + biases[p][q];
            this.val = pow((1 + exp(-this.val)), -1);
            neurons[p][q] = this.val;
        }
    }
    return neurons[layers.length - 1][0];
};

constructnetwork();
println(forwardpropagation(input));

