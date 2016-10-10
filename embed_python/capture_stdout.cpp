#include <stdio.h>

#include <Python.h>

int main(int ac, char **av)
{
	int rc = -1, i;

	PyObject *pModule, *pFunc, *pValue, *pArgs, *pStdout;

	Py_SetProgramName(av[0]);
	Py_Initialize();
		
	PyObject *pModuleStringIO = PyImport_ImportModule("StringIO");
	PyObject *pFuncStringIO = PyObject_GetAttrString(pModuleStringIO, "StringIO");
	PyObject *pArgs = PyTuple_new(0);
	PyObject *pObjStringIo = PyObject_CallObject(pFuncStringIO, pArgs);

	pStdout = PySys_GetObject("stdout");
	if(!pStdout) { printf("ERROR: PySys_GetObject()\n"); goto cleanup; }
	int retVal = PySys_SetObject("stdout", pObjStringIo);
	if(retVal) { printf("ERROR: PySys_SetObject()\n"); goto cleanup; }

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

	Py_Finalize();
	rc = 0;
	cleanup:
	return rc;
}
