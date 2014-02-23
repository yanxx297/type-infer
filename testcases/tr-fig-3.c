unsigned f(int arg1, int arg2, int arg3) {
    int s1 = arg2 / arg3;
    int s2 = arg1 / arg3;
    int s3 = arg1 / arg2;

    int a1 = s1;
    int a2 = s2;
    int a3 = s3;

    int b1 = a1 + a2 + a3;
    int b2 = a1 ^ a2 ^ a3;

    unsigned u1 = (unsigned)b1;
    unsigned u2 = (unsigned)b2;
    
    u1 /= u2;
    u2 /= u1;
    return u1 + u2;
}

int main(int argc, char **argv) {
    return f(1, 2, 3);
}
