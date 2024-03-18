var tmp_lz, tmp_lz_stop, tmp_lz_j, tmp_cp;
var a = [
    undefined,                            // I don't like a[0]
    [1, 2, 0, 0, 0, 1, 0, 6, 4, 5],       // a[i][0] represents b[i]
    [2, 0, 0, 1, 6, 8, 0, 14, 8, 0],      // this is a 9 by 9 system
    [9, 0, 0, 5, 0, 3, 4, 0, 0, 6],
    [3, 0, 4, 0, 8, 0, 2, 5, 0, 0],
    [4, 6, 8, 0, 0, 0, 3, 9, 2, 0],
    [0, 3, 0, 2, 7, 0, 0, 8, 0, 0],
    [8, 9, 0, 0, 5, 2, 0, 6, 0, 0],
    [0, 0, 1, 0, 8, 7, 6, 9, 0, 0],
    [0, 5, 0, 0, 5, 9, 4, 5, 7, 8]
    ];

var leadingzeroes = function(r){
    tmp_lz = 0; tmp_lz_stop = 0; tmp_lz_j = 0;
    while (tmp_lz_stop === 0){
        tmp_lz_j += 1;
        if (r[tmp_lz_j] === 0){tmp_lz += 1;}
        if (r[tmp_lz_j] !== 0 /*|| tmp_lz_j >= r.length - 1*/){tmp_lz_stop = 1;}
    }
    return tmp_lz;
};

var compare = function(r1, r2){return leadingzeroes(r1) - leadingzeroes(r2);};

var pushcycle = function(R){
    for (var i = R.length - 1; i > 0; i--){
        R[i] = R[i - 1];
    }
    R[0] = undefined;
    return R;
};

a = pushcycle(a.sort(compare));
