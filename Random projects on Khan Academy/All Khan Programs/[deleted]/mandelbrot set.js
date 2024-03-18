var z_init = [0, 0];
var ite1 = 100, ite2 = 100;
var z_val = z_init; var r;

var rbin = function (r, i) {
    var ret = 1;
    for (var k = 1; k <= i; k++){
        ret = ret * (r - k + 1) / (i - k + 1);
    }
    return ret;
};
var vpow = function (r) {
    return [cos(180*r), sin(180*r)];
};
var ipow = function(r) {
    return [cos(90*r), sin(90*r)];
};
/*var rpow = function (a, b) {
    if (a > 0 
};*/
var zadd = function (z1, z2) {
    return [z1[0] + z2[0], z1[1]+ z2[1]];
};
var zmur = function (r, z) {
    return [r * z[0], r * z[1]];
};
var zmul = function (z1, z2) {
    return ([z1[0]*z2[0] - z1[1]*z2[1], z1[0]*z2[1] + z1[1]*z2[0]]);
};
var zpon = function (z, n) {
    var ret = [1, 0];
    for (var k = 1; k <= n; k++){ret = zmul(ret, z);}
    return ret;
};
var zpow = function (z, r) {
    var ret = [0, 0];
    if (z[0] > 0) {
        for (var k = 0; k <= ite1; k++){
            ret = zadd(ret, zmur(rbin(r,k), zmur(pow(z[0],r-k), zpon(zmur(z[1],[0,1]), k))));
        }
    }
    if (z[0] < 0) {
        for (var k = 0; k <= ite1; k++){
            ret = zmul(vpow(r), zadd(ret, zmur(rbin(r,k), zmur(pow(-z[0],r-k), zpon(zmur(-z[1],[0,1]), k)))));
        }
    }
    if (z[0] === 0) {
        if (z[1] > 0) {
            ret = zmur(pow(z[1], r), ipow(r));
        }
        if (z[1] < 0) {
            ret = zmul(vpow(r), zmur(pow(-z[1], r), ipow(r)));
        }
        if (z[1] === 0){
            ret = 0;
        }
    }
    return ret;
};

var draw = function() {
    for (var i = -2; i <= 1; i+= 0.01){
        for (var j = -1; j <= 1; j += 0.01){
            z_val = z_init;
            r = mouseX/200;
            for (var k = 0; k < ite2; k++){
                z_val = zadd (zpow(z_val, r), );
                
            }
        }
    }
};