// demonstrates:
// - loading an assembly from a file
// - enumerating the classes in that assembly
// - enumerating the methods in those classes
// - calling a method

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
			var pwd = Path.GetDirectoryName(Assembly.GetExecutingAssembly().Location);
			Console.WriteLine("pwd: {0}", pwd);

			var fpath = pwd + "/" + "create-objects.exe";
			Console.WriteLine("fpath: {0}", fpath);

			var assembly = Assembly.LoadFile(fpath);
			
			foreach (var type in assembly.GetTypes())
			{
				Console.WriteLine("type: {0}", type);

				foreach (var meth in type.GetMethods())
				{
					Console.WriteLine("   method: {0}", meth);
				}
			}

			// call methods!
			var class_ = assembly.GetType("SomeType");
			var instance = Activator.CreateInstance(class_);

			// show single argument, using reflection methods
			assembly.GetType("SomeType").GetMethod("DoSomething").Invoke(instance, new object[] {5});

			// show no argument, using reflection methods
			assembly.GetType("SomeType").GetMethod("DoSomethingElse").Invoke(instance, new object[] {});

			// using unwrap
			// (requires you reference the assembly during compilation to declare a SomeType)
			ObjectHandle oh = Activator.CreateInstanceFrom(assembly.CodeBase, "SomeType");
			SomeType st = (SomeType) oh.Unwrap();
			st.DoSomething(5);
			st.DoSomethingElse();
		}
	}
}
