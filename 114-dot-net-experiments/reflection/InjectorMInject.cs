// Use Minject to inject
//
// couldn't get it to work, crash at MonoProcess.Attach()

using System;
using System.IO;
using System.Diagnostics;

using MInject;

namespace InjectorNamespace
{
	public class InjectorClass
	{
		public static void Main(string[] args)
		{
			var pid = int.Parse(args[0]);
			Console.WriteLine("attaching to pid: {0}", pid);

			Process targetProcess = Process.GetProcessById(pid);
			Console.WriteLine("targetProcess: {0}", targetProcess);

			MonoProcess monoProcess;

			Console.WriteLine("A");

			//Try to attach to targetProcess Mono module
			if (MonoProcess.Attach(targetProcess, out monoProcess))
			{
				Console.WriteLine("B");

    			byte[] assemblyBytes = File.ReadAllBytes("Injected.dll");

				Console.WriteLine("C");

    			IntPtr monoDomain = monoProcess.GetRootDomain();
    			monoProcess.ThreadAttach(monoDomain);
    			monoProcess.SecuritySetMode(0);

				Console.WriteLine("D");

    			//Disable AssemblyLoad callbacks before injection
    			monoProcess.DisableAssemblyLoadCallback();

				Console.WriteLine("E");

    			IntPtr rawAssemblyImage = monoProcess.ImageOpenFromDataFull(assemblyBytes);
    			IntPtr assemblyPointer = monoProcess.AssemblyLoadFromFull(rawAssemblyImage);
    			IntPtr assemblyImage = monoProcess.AssemblyGetImage(assemblyPointer);
    			IntPtr classPointer = monoProcess.ClassFromName(assemblyImage, "InjectedNamespace", "InjectedClass");
    			IntPtr methodPointer = monoProcess.ClassGetMethodFromName(classPointer, "InjectedMethod");

    			//Finally invoke the TestInjection.Loader.Init method
    			monoProcess.RuntimeInvoke(methodPointer);

    			//Restore the AssemblyLoad callbacks to avoid weird behaviours
    			monoProcess.EnableAssemblyLoadCallback();    

    			//You MUST dispose the MonoProcess instance when finished
    			monoProcess.Dispose();
			}
		}
	}
}
