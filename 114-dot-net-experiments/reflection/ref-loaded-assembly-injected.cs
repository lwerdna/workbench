// demonstrates finding an already-loaded assembly in memory

using System; // for class "Activator"
using System.IO; // for class "Path"
using System.Runtime.Remoting; // for class "ObjectHandle"
using System.Reflection; // for class "Assembly"
using System.Threading;

namespace InjectedNamespace
{
	public class InjectedClass
	{
		public static void InjectedMethodWorker()
		{
			Console.WriteLine("STAGE2: InjectedMethodWorker()");

			//
			// iterate over all assemblies
			//
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

					PropertyInfo[] properties = type.GetProperties(BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic);
					for (int i=0; i<properties.Length; ++i)
					{
						Console.WriteLine("STAGE2:     properties: {0}", properties[i].ToString());
					}
				}
			}
		}

		public static void InjectedMethod()
		{
			Console.WriteLine("STAGE2: InjectedMethod()");

			Thread thread = new Thread(new ThreadStart(InjectedMethodWorker));
			thread.Start();
		}
	}
}
