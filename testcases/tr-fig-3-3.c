unsigned f(int arg1, int arg2, int arg3) {
    int s1 = arg1 / 3;
    int s2 = arg2 / 3;
    int s3 = arg3 / 3;

    int a1 = s1;
    int a2 = s2;
    int a3 = s3;

    int b1 = a1 + a2 + a3;
    int b2 = a1 ^ a2 ^ a3;

    unsigned u1 = (unsigned)b1;
    unsigned u2 = (unsigned)b2;
    
    u1 /= 3;
    u2 /= 3;
    return u1 + u2;
}

int main(int argc, char **argv) {
    return f(1, 2, 3);
}
