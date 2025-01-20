// demonstrates finding an already-loaded assembly in memory

using System; // for class "Activator"
using System.IO; // for class "Path"
using System.Runtime.Remoting; // for class "ObjectHandle"
using System.Reflection; // for class "Assembly"

namespace ExampleNamespace
{
	public class ExampleClass
	{
		public static void Main()
		{
			//
			// load the "create-objects" assembly
			//
			var pwd = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
			Console.WriteLine("pwd: {0}", pwd);

			var fpath = pwd + "/" + "create-objects.exe";
			Console.WriteLine("fpath: {0}", fpath);

			Assembly.LoadFile(fpath);

			//
			// iterate over all assemblies
			//
			foreach (var assembly in AppDomain.CurrentDomain.GetAssemblies())
			{
				Console.WriteLine("assembly: {0}", assembly);

				foreach (var type in assembly.GetTypes())
				{
					Console.WriteLine("  type: {0}", type);
	
					foreach (var meth in type.GetMethods())
					{
						Console.WriteLine("    method: {0}", meth);
					}

					PropertyInfo[] properties = type.GetProperties(BindingFlags.Instance | BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic);
					for (int i=0; i<properties.Length; ++i)
					{
						Console.WriteLine("    properties: {0}", properties[i].ToString());
					}
				}
			}
		}
	}
}
