//
// from:
//   https://learn.microsoft.com/en-us/dotnet/api/system.activator?view=net-9.0
//
// compile/run:
//   mono-csc foo.cs -out:foo.exe
//   mono foo.exe
//
using System;
using System.Reflection;
using System.Text;

public class SomeType
{
    public void DoSomething(int x)
    {
        Console.WriteLine("100 / {0} = {1}", x, 100 / x);
    }

    public void DoSomethingElse()
    {
		Console.WriteLine("hey there");
    }
}

public class Example
{
    static void Main()
    {
        // Create an instance of the StringBuilder type using
        // Activator.CreateInstance.
        Object o = Activator.CreateInstance(typeof(StringBuilder));

        // Append a string into the StringBuilder object and display the
        // StringBuilder.
        StringBuilder sb = (StringBuilder) o;
        sb.Append("Hello, there.");
        Console.WriteLine(sb);

        // Create an instance of the SomeType class that is defined in this
        // assembly.
        System.Runtime.Remoting.ObjectHandle oh =
            Activator.CreateInstanceFrom(Assembly.GetEntryAssembly().CodeBase,
                                         typeof(SomeType).FullName);

		Console.WriteLine(typeof(SomeType).FullName);

        // Call an instance method defined by the SomeType type using this object.
        SomeType st = (SomeType) oh.Unwrap();

        st.DoSomething(5);
    }
}
