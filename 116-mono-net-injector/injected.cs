using System;
using System.Threading;
using System.Diagnostics;

namespace Test
{
	public class Test
	{
		public static void Worker()
		{
			foreach (var assembly in AppDomain.CurrentDomain.GetAssemblies())
			{
				Console.WriteLine("STAGE2: assembly: {0}", assembly);

				foreach (var type in assembly.GetTypes())
				{
					Console.WriteLine("STAGE2:   type: {0}", type);
	
					foreach (var meth in type.GetMethods())
					{
						Console.WriteLine("STAGE2:     method: {0}", meth);
					}
				}
			}

		}

		public static void TestMethod()
		{
			int pid = System.Diagnostics.Process.GetCurrentProcess().Id;

			Console.WriteLine("STAGE2: I'm inside pid {0}!", pid);

	        Thread thread = new Thread(new ThreadStart(Worker));
	        thread.Start();
		}
	}
}
