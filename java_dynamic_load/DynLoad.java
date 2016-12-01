import java.lang.reflect.Field;

import java.net.URL;
import java.net.URLClassLoader;
import java.net.MalformedURLException;

public class DynLoad
{
	public static void main(String[] args) 
	{
		try {
			//URL url = new URL("file:///Users/andrewl/repos/lwerdna/experiments/java_dynamic_load");
			URL url = new URL("file://.");
			
			URL[] urls = {url};

    		ClassLoader classLoader = new URLClassLoader(urls);

    		Class c = classLoader.loadClass("Injected");

			for(Field f: c.getDeclaredFields()) {
				System.out.println("found field: " + f.getName());
			}

			Injected obj = (Injected) c.newInstance();
			obj.go();

		} catch (MalformedURLException e) {
			System.out.println(e);
		} catch (ClassNotFoundException e) {
			System.out.println(e);
		} catch (InstantiationException e) {
			System.out.println(e);
		} catch (IllegalAccessException e) {
			System.out.println(e);
		}

		System.out.println("It worked!");
	}
}
