// Algorithm:
// 1. Create lookup table containing the best (highest) price is available in the future.
//    ie: lookup[i] is the highest price available in prices[k], k>=i
// 2. Scan left to right, tracking the maximum distance between current buy prices and maximum future sell price.
//
// This is too concrete a way of thinking, imagining past and present, when really we have an array of numbers.
//
class Solution1
{
	public int maxProfit(int[] prices)
	{
		int[] lookup = new int[prices.length];

		int maximum = 0;
		for(int i=prices.length-1; i>=0; i=i-1)
		{
			lookup[i] = maximum = Math.max(prices[i], maximum);
		}

		int record = 0;
		for(int i=0; i<prices.length-1; i++)
		{
			record = Math.max(record, lookup[i] - prices[i]);
		}

		return record;
	}

	public static void main(String[] args)
	{
		int result;

		Solution1 sol = new Solution1();

		// solve problem 1
		int[] problem1 = {7,1,5,3,6,4};
		result = sol.maxProfit(problem1);
		System.out.println(result);

		// solve problem 2
		int[] problem2 = {7,6,4,3,1};
		result = sol.maxProfit(problem2);
		System.out.println(result);
	}
}


