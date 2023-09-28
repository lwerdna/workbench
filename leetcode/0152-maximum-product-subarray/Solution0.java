class Solution0
{
    public int maxProduct(int[] nums)
    {
    	int record = nums[0];
    	int lastmax = 1;
    	int lastmin = 1;
    	for (int x:nums)
    	{
    		int y = x*lastmax;
    		int z = x*lastmin;
    		lastmax = Math.max(x, Math.max(y, z));
    		lastmin = Math.min(x, Math.min(y, z));
    		if (lastmax > record)
    			record = lastmax;

			/*
    		System.out.println(x + ", " + y + ", " + z);
    		System.out.println("lastmax: " + lastmax);
    		System.out.println("lastmin: " + lastmin);
    		*/
    	}

    	return record;
    }

	public static void main(String[] args)
	{
		int result;

		Solution0 sol = new Solution0();

		int[] problem1 = {2,3,-2,4};
		result = sol.maxProduct(problem1);
		System.out.println("expect 6: " + result);

		int[] problem2 = {-2,0,-1};
		result = sol.maxProduct(problem2);
		System.out.println("expect 0: " + result);

		int[] problem3 = {-2, -3, 4, 5, -6};
		result = sol.maxProduct(problem3);
		System.out.println("expect 360: " + result);

		int[] problem4 = {-2};
		result = sol.maxProduct(problem4);
		System.out.println("expect -2: " + result);

		int[] problem5 = {2};
		result = sol.maxProduct(problem5);
		System.out.println("expect 2: " + result);
	}
}
