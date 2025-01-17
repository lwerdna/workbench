using System;
using System.Threading;
using System.Diagnostics;

namespace InjectedNamespace
{
	public class InjectedClass
	{
		public static void InjectedMethod()
		{
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
