clear, clc;

n = 100;
mat = zeros(n + 1, n + 1);
vec = zeros(n + 1, 0);

vec(2, 1) = 1;
for i = 0:n
    for j = 0:n
        mat(i + 1, j + 1) = (1 - (-1) ^ (i + j + 1)) / (i + j + 1) * mf(n) ^ (i + j + 1);
    end
end

a = mat\vec;
pola = fliplr(a');

x = -mf(n):0.001:mf(n);
plot(x, polyval(pola, x));

function m = mf (n)
    m = n^0.5;
end
