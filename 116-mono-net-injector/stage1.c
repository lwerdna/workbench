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
typedef void* (*mono_class_from_name)(void* image, char* namespacee, char* name);
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

void load_assembly_call_method(char *assembly_path)
{
	printf("STAGE1: assembly_path: %s\n", assembly_path);

	void *handle = dlopen(NULL, RTLD_NOW);
	printf("STAGE1: mono-sgen handle: %p\n", handle);

    do_mono_thread_attach = (mono_thread_attach)(dlsym(handle, "mono_thread_attach"));
    do_mono_get_root_domain = (mono_get_root_domain)(dlsym(handle, "mono_get_root_domain"));
    do_mono_assembly_open = (mono_assembly_open)(dlsym(handle, "mono_assembly_open"));
    do_mono_assembly_get_image = (mono_assembly_get_image)(dlsym(handle, "mono_assembly_get_image"));
    do_mono_class_from_name = (mono_class_from_name)(dlsym(handle, "mono_class_from_name"));
    do_mono_class_get_method_from_name = (mono_class_get_method_from_name)(dlsym(handle, "mono_class_get_method_from_name"));
    do_mono_runtime_invoke = (mono_runtime_invoke)(dlsym(handle, "mono_runtime_invoke"));

    do_mono_thread_attach(do_mono_get_root_domain());
    void* assembly = do_mono_assembly_open(assembly_path, NULL);
    void* Image = do_mono_assembly_get_image(assembly);
    void* MonoClass = do_mono_class_from_name(Image, "Test", "Test");
    void* MonoClassMethod = do_mono_class_get_method_from_name(MonoClass, "TestMethod", 0);

    do_mono_runtime_invoke(MonoClassMethod, NULL, NULL, NULL);
}
