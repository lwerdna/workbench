#include <stdio.h>

#include <Python.h>

int main(int ac, char **av)
{
	int rc = -1;

	PyObject *mod, *func, *obj, *str;

	Py_SetProgramName(av[0]);
	Py_Initialize();
	
	// create StringIO object	
	mod = PyImport_ImportModule("StringIO");
	func = PyObject_GetAttrString(mod, "StringIO");
	obj = PyObject_CallObject(func, PyTuple_New(0));

	// set sys.stdout to that StringIO object
	PySys_SetObject("stdout", obj);

	// run some python
	PyRun_SimpleString("print \"I'm in python.\"");
	printf("-- done running python --\n");

	// see if we captured that stdout
	printf("-- retrieving its stdout --\n");
	func = PyObject_GetAttrString(obj, "getvalue");
	str = PyObject_CallObject(func, PyTuple_New(0));
	printf("%s\n", PyString_AsString(str));

	// cleanup, Py_DECREF, blah blah
	Py_Finalize();
	rc = 0;
	return rc;
}
