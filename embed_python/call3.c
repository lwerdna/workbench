#include <stdio.h>

#include <Python.h>

int main(int ac, char **av)
{
	int rc = -1, i, n;
	const char *modNames[3] = {"a", "b", "c"};

	PyObject *pModule, *pFunc, *pValue, *pTuple, *pArgs;

	Py_SetProgramName(av[0]);
	Py_Initialize();

	/* find out what builtin modules exist */
	pModule = PyImport_ImportModule("sys");
	if(!pModule) {
		printf("ERROR: PyImport_ImportModule(\"sys\")\n");
		goto cleanup;
	}
	
	pTuple = PyObject_GetAttrString(pModule, "builtin_module_names");

	n = PyTuple_Size(pTuple);
	for(i=0; i<n; ++i) {
		PyObject *pString = PyTuple_GetItem(pTuple, i);
		printf("builting module %d/%d: %s\n", i+1, n,
			PyString_AsString(pString));
	}

	/* call the local modules */	
	for(i=0; i<3; ++i) {
		printf("on module: %s\n", modNames[i]);

		pModule = PyImport_ImportModule(modNames[i]);
		if(!pModule) {
			printf("ERROR: PyImport_ImportModule()\n");
			goto cleanup;
		}

		pFunc = PyObject_GetAttrString(pModule, "go");
		if(!pFunc) {
			printf("ERROR: PyObject_GetAttrString()\n");
			goto cleanup;
		}

		pArgs = PyTuple_New(0);
		if(!pArgs) {
			printf("ERROR: PyTuple_New()\n");
			goto cleanup;
		}

		pValue = PyObject_CallObject(pFunc, pArgs);
		Py_DECREF(pArgs);
		Py_DECREF(pFunc);
		printf("Result of call: %ld\n", PyInt_AsLong(pValue));
		Py_DECREF(pValue);
	}

	Py_Finalize();
	rc = 0;
	cleanup:
	return rc;
}
