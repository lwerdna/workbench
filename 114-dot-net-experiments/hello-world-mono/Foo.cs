// call function from class Bar

// use the System namespace which has the Console, Environment, Int32, String classes
// https://learn.microsoft.com/en-us/dotnet/api/system?view=net-9.0
using System;

public static class Foo
{
    public static int Main()
    {
        Console.WriteLine("Hello, world!\n");

        string[] argv = Environment.GetCommandLineArgs();
        int argc = argv.Length;

        Console.WriteLine(String.Format("argc: {0}", argc));
        for (int i=0; i < argc; i++)
            Console.WriteLine(String.Format("argv[{0}]: {1}", i, argv[i]));

        int val = 7;
        if (argc > 1)
        	val = Int32.Parse(argv[1]);

		int squared = Bar.square(val);

        Console.WriteLine(String.Format("{0} squared is: {1}", val, squared));

        return 0;
    }
}
