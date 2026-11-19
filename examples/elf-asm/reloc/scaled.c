extern int scale(int);
extern int bias;
int scaled_plus_bias(int x) { return scale(x) + bias; }
