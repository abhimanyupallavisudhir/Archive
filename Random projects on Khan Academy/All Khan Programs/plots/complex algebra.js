var x_coerce_z = function (x){
    return [x, 0];
};
var y_coerce_z = function (y){
    return [0, y];
};
var z_add_z = function (z1, z2){
    return [z1[0] + z2[0], z1[1] + z2[1]];
};
var z_mul_z = function (z1, z2){
    return [z1[0] * z2[0] - z1[1] * z2[1], z1[0] * z2[1] + z1[1] * z2[0]];
};
var z_pow_n = function (z, n){
    var prod = [1, 0];
    for (var i = 0; i < n; i++){
        prod = z_mul_z(prod, z);
    }
    return prod;
};
var neg_z = function (z){
    return [-z[0], -z[1]];
};
var z_sub_z = function(z1, z2){
    return z_add_z(z1, neg_z(z2));
};
var z_norm = function (z){
    return pow(pow(z[0], 2) + pow(z[1], 2), 1/2);
};
var z_conj = function (z){
    return [z[0], -z[1]];
};
var inv_z = function (z){
    return z_mul_z(z_conj(z), x_coerce_z(pow(z_norm(z), -2)));
};
var z_div_z = function (z1, z2){
    return z_mul_z(z1, inv_z(z2));
};