using System;
using System.Threading;
using System.Diagnostics;

namespace Test
{
	public class Test
	{
		public static void TestMethod()
		{
			int pid = System.Diagnostics.Process.GetCurrentProcess().Id;

			Console.WriteLine("STAGE2: I'm inside pid {0}!", pid);
		}
	}
}
