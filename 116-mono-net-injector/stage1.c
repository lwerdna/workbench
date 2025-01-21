// https://journal.lunar.sh/2020/mono-dot-net-injection.html
// https://github.com/warbler/SharpMonoInjector/blob/master/src/SharpMonoInjector/Injector.cs

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include <dlfcn.h>

typedef void* (*mono_thread_attach)(void* domain);
typedef void* (*mono_get_root_domain)();
typedef void* (*mono_assembly_open)(char* file, void* stat);
typedef void* (*mono_assembly_get_image)(void* assembly);
typedef void* (*mono_class_from_name)(void* image, char* namespace, char* name);
typedef void* (*mono_class_get_method_from_name)(void* classs, char* name, unsigned int param_count);
typedef void* (*mono_runtime_invoke)(void* method, void* instance, void* *params, void* exc);

mono_get_root_domain do_mono_get_root_domain;
mono_assembly_open do_mono_assembly_open;
mono_assembly_get_image do_mono_assembly_get_image;
mono_class_from_name do_mono_class_from_name;
mono_class_get_method_from_name do_mono_class_get_method_from_name;
mono_runtime_invoke do_mono_runtime_invoke;
mono_thread_attach do_mono_thread_attach;

__attribute__ ((constructor))
static void init(int argc, char **argv)
{
	printf("STAGE1: Hello!\n");
}

#define ERRCLEANUP(MSG) { printf("STAGE1: ERROR: " MSG "\n"); goto cleanup; }

void load_assembly_call_method(char *assembly_path, char *namespace, char *class, char *method)
{
	printf("STAGE1: assembly_path: %s\n", assembly_path);
	printf("STAGE1:     namespace: %s\n", namespace);
	printf("STAGE1:         class: %s\n", class);
	printf("STAGE1:        method: %s\n", method);

	void *handle = dlopen(NULL, RTLD_NOW);
	if (handle == NULL) ERRCLEANUP("dlopen()");
	//printf("STAGE1: mono-sgen handle: %p\n", handle);

    do_mono_thread_attach = (mono_thread_attach)(dlsym(handle, "mono_thread_attach"));
	if (do_mono_thread_attach == NULL) ERRCLEANUP("dlsym() resolving mono_thread_attach()");
	//printf("STAGE1: do_mono_thread_attach: %p\n", do_mono_thread_attach);

    do_mono_get_root_domain = (mono_get_root_domain)(dlsym(handle, "mono_get_root_domain"));
	if (do_mono_get_root_domain == NULL) ERRCLEANUP("dlsym() resolving mono_get_root_domain()");
	//printf("STAGE1: do_mono_get_root_domain: %p\n", do_mono_get_root_domain);

    do_mono_assembly_open = (mono_assembly_open)(dlsym(handle, "mono_assembly_open"));
	//printf("STAGE1: do_mono_assembly_open: %p\n", do_mono_assembly_open);
	if (do_mono_assembly_open == NULL) ERRCLEANUP("dlsym() resolving mono_assembly_open()");

    do_mono_assembly_get_image = (mono_assembly_get_image)(dlsym(handle, "mono_assembly_get_image"));
	//printf("STAGE1: do_mono_assembly_get_image: %p\n", do_mono_assembly_get_image);
	if (do_mono_assembly_get_image == NULL) ERRCLEANUP("dlsym() resolving mono_assembly_get_image()");

    do_mono_class_from_name = (mono_class_from_name)(dlsym(handle, "mono_class_from_name"));
	//printf("STAGE1: do_mono_class_from_name: %p\n", do_mono_class_from_name);
	if (do_mono_class_from_name == NULL) ERRCLEANUP("dlsym() resolving mono_class_from_name()");

    do_mono_class_get_method_from_name = (mono_class_get_method_from_name)(dlsym(handle, "mono_class_get_method_from_name"));
	//printf("STAGE1: do_mono_class_get_method_from_name: %p\n", do_mono_class_get_method_from_name);
	if (do_mono_class_get_method_from_name == NULL) ERRCLEANUP("dlsym() resolving mono_class_get_method_from_name()");

    do_mono_runtime_invoke = (mono_runtime_invoke)(dlsym(handle, "mono_runtime_invoke"));
	//printf("STAGE1: do_mono_runtime_invoke: %p\n", do_mono_runtime_invoke);
	if (do_mono_runtime_invoke == NULL) ERRCLEANUP("dlsym() resolving mono_runtime_invoke()");

	printf("STAGE1: calling mono_thread_attach()\n");
    do_mono_thread_attach(do_mono_get_root_domain());

	printf("STAGE1: calling mono_assembly_open(\"%s\")\n", assembly_path);
    void *assembly = do_mono_assembly_open(assembly_path, NULL);
    if (assembly == NULL) ERRCLEANUP("acquiring assembly");
    //printf("STAGE1: assembly = %p\n", assembly);

	printf("STAGE1: calling mono_assembly_get_image(%p)\n", assembly);
    void *Image = do_mono_assembly_get_image(assembly);
    if (Image == NULL) ERRCLEANUP("acquiring image");
    //printf("STAGE1: Image = %p\n", Image);

	printf("STAGE1: calling mono_class_from_name(%p, \"%s\", \"%s\")\n", Image, namespace, class);
    void *MonoClass = do_mono_class_from_name(Image, namespace, class);
    if (MonoClass == NULL) ERRCLEANUP("acquiring class");
    //printf("STAGE1: MonoClass = %p\n", MonoClass);

	printf("STAGE1: calling mono_class_get_method_from_name(%p, \"%s\", 0)\n", MonoClass, method);
    void *MonoClassMethod = do_mono_class_get_method_from_name(MonoClass, method, 0);
    if (MonoClassMethod == NULL) ERRCLEANUP("acquiring method");
    //printf("STAGE1: MonoClassMethod = %p\n", MonoClassMethod);

	printf("STAGE1: calling do_mono_runtime_invoke()\n");
    do_mono_runtime_invoke(MonoClassMethod, NULL, NULL, NULL);

    cleanup:
    return;
}
