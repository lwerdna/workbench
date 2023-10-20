class Solution
{
	String slicer(String input, int left, int right)
	{
		if (left > input.length() || right < 0)
			return "";
		if (left < 0)
			left = 0;
		if (right > input.length())
			right = input.length();

	    return input.substring(left, right);
	}

    public int strStr(String haystack, String needle)
    {
        for(int i=0; i<haystack.length(); i++)
        {
            String slice = this.slicer(haystack, i, i+needle.length());

            if (slice.equals(needle))
            	return i;
        }
        return -1;
    }

	public static void main(String[] args)
	{
		Solution sol = new Solution();

		// solve problem 1
		String haystack = "sadbutsad";
		String needle = "sad";
		int result = sol.strStr(haystack, needle);
		System.out.println(result);
	}
}
