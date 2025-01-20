using System;
using System.Threading;
using System.Diagnostics;

namespace InjecteeNamespace
{
	public class InjecteeClass
	{
		string name = "MyName";
		int age = 77;

		public static void Main(String[] args)
		{
			if (args.Length > 0)
				Console.WriteLine("args[0]: {0}", args[0]);
			if (args.Length > 1)
				Console.WriteLine("args[1]: {0}", args[1]);

			int pid = System.Diagnostics.Process.GetCurrentProcess().Id;

			for (int i=0; i<5*60; ++i)
			{
				Console.WriteLine("Hello, world! (pid: {0})", pid);

				Thread.Sleep(1000);
			}
		}

		public void FunkyMonkey()
		{
			Console.WriteLine("Funky Monkey is here!");
		}
	}
}
