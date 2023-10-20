// Algorithm:
// 1. For every pair of numbers a,b where a occurs before b, calculate the maximum difference between sell and buy.
//
// naive O(n^2) solution, times out on a test case with 67552 prices in it
//
class Solution0
{
	public int maxProfit(int[] prices)
	{
		int record = 0;
		for(int i=0; i<prices.length-1; i++)
		{
			for(int j=i+1; j<prices.length; j++)
			{
				int profit = prices[j] - prices[i];
				if (profit > record)
				{
					record = profit;
				}
			}
		}

		return record;
	}

	public static void main(String[] args)
	{
		int result;

		Solution0 sol = new Solution0();

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


