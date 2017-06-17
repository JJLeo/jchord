public class T {
	static int[] g;
	static int c = 5;
    public static void main(String[] args) {
		A a = new A();
		a.f = null;
		g = new int[5];
		for (int i = 0; i < c; i++) {
			g[i] += a.f[i];
		}
	}
}

class A {
	public int[] f = new int[10];
	public A() {
		this.f = new int[5];
	}
}

