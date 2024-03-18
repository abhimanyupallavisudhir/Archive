var costApproximator = [[2, 1, 4, 2, 1, 6, 21, 11, 21, 41]]; //0th row are just soldier costs
var currCost, currSolcostrem, currCostext, currEpted, currTrials;

var costInitialise = function() {
    for (var j = 0; j < costApproximator[0].length; j++){
        //find minimum cost -- substitute the most inefficient strategies
        //                  -- displace a number of soldiers <= itself
        costApproximator[1] = [];
        costApproximator[1][j] = [];
        currSolcostrem = costApproximator[0][j];
        currTrials = 0;
        currEpted = [];
        for (var j2 = 0; j2 < costApproximator[0].length; j2++){
            currEpted[j2] = 0;
        }
        currEpted[j] = 1;
        currCost = 0;
        while (currTrials < 12) {
            currCostext = [0, 0];
            for (var j1 = 0; j1 < costApproximator[0].length; j1++){
                if (currEpted[j1] === 0 && currSolcostrem - costApproximator[0][j1] > 0){
                    if (costApproximator[0][j1]/(j1 + 1) > currCostext[1]){
                        currCostext[0] = j1 + 1;
                        currCostext[1] = costApproximator[0][j1]/(j1 + 1);
                    }
                }
            }
            currEpted[currCostext[0] - 1] = 1;
            currSolcostrem -= currCostext[0] * currCostext[1];
            currCost += currCostext[0];
            currTrials++;
        }
        costApproximator[1][j][0] = currCost;
        
    }
};
costInitialise();