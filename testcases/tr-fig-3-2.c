unsigned f1(int s1, int s2, int s3) {
	unsigned a1 = s2/s3;
	unsigned a2 = s1/s3;

	unsigned b1 = a1 + a2;
	unsigned b2 = a1 ^ a2;
	unsigned b3 = a1 - a2;
	unsigned u1 = b1;
	unsigned u2 = b2;
	unsigned u3 = b3;
	u1 /= u2;
	u2 /= u3;
	u3 /= u1;
	return u1 + u2 + u3;
}

unsigned f2(int s1, int s2, int s3) {
	int a1 = s2/s3;
	int a2 = s1/s3;

	int b1 = a1 + a2;
	int b2 = a1 ^ a2;
	int b3 = a1 - a2;
	unsigned u1 = b1;
	unsigned u2 = b2;
	unsigned u3 = b3;
	u1 /= u2;
	u2 /= u3;
	u3 /= u1;
	return u1 + u2 + u3;

}

int main(int argc, char **argv) {
	f1(1, 2, 3);
	f2(1, 2, 3);
	return 0;
}
