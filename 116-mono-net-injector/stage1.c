
#include <stdio.h>
#include <stdlib.h>

#include <dlfcn.h>

void *mono_get_root_domain;
void *mono_thread_attach;
void *mono_image_open_from_data;
void *mono_assembly_load_from_full;
void *mono_assembly_get_image;
void *mono_class_from_name;
void *mono_class_get_method_from_name;
void *mono_runtime_invoke;
void *mono_assembly_close;
void *mono_image_strerror;
void *mono_object_get_class;
void *mono_class_get_name;

void *read_file_to_buffer(char *fpath)
{
    FILE *file;
    char *buffer;
    long file_size;

    printf("opening %s\n", fpath);
    file = fopen(fpath, "rb");
    if (file == NULL) {
        perror("Error opening file");
        return NULL;
    }

    fseek(file, 0, SEEK_END);
    file_size = ftell(file);
    rewind(file);

    // Allocate memory for the buffer
    printf("allocating %ld bytes\n", file_size);
    buffer = (char *)malloc(file_size);
    if (buffer == NULL) {
        perror("Error allocating memory");
        fclose(file);
        return NULL;
    }

    // Read the file into the buffer
    printf("reading %ld bytes\n", file_size);
    size_t bytes_read = fread(buffer, 1, file_size, file);
    if (bytes_read != file_size) {
        perror("Error reading file");
        fclose(file);
        free(buffer);
        return NULL;
    }

    // Close the file and free the memory
    printf("closing\n");
    fclose(file);

    printf("returning %p\n", buffer);
    return buffer;
}

__attribute__ ((constructor))
static void init(int argc, char **argv)
{
	printf("Hello from injected!\n");
}

void load_assembly_call_method(char *assembly_path, char *namespace, char *class, char *method)
{
	printf("assembly_path: %s\n", assembly_path);
	printf("namespace: %s\n", namespace);
	printf("class: %s\n", class);
	printf("method: %s\n", method);

	//void *handle = dlopen("/usr/bin/mono-sgen", RTLD_NOW);
	//void *handle = dlopen("libmono-native.so.0.0.0", RTLD_NOW);
	void *handle = dlopen(NULL, RTLD_NOW);
	printf("handle: %p\n", handle);

	void *tmp;

	// resolve needed symbols in mono
	void *(*mono_get_root_domain)(void) = dlsym(handle, "mono_get_root_domain");
	if (mono_get_root_domain==NULL) { printf("ERROR: resolving symbol mono_get_root_domain\n"); return; }

	tmp = dlsym(handle, "mono_thread_attach");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_image_open_from_data");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_assembly_load_from_full");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_assembly_get_image");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_class_from_name");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_class_get_method_from_name");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_runtime_invoke");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_assembly_close");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_image_strerror");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_object_get_class");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }
	tmp = dlsym(handle, "mono_class_get_name");
	if (tmp==NULL) { printf("ERROR: resolving symbol\n"); return; }

	// mono interaction strategy from: https://github.com/warbler/SharpMonoInjector

	// MonoDomain *mono_get_root_domain (void)
	void *root_domain = mono_get_root_domain();
	printf("root_domain: %p\n", root_domain);

	// MonoImage *mono_image_open_from_data (char *data, uint32_t data_len, mono_bool need_copy, MonoImageOpenStatus *status);
	void *buf = read_file_to_buffer(assembly_path);
	printf("file read to: %p\n", buf);
	int status;

	//void *raw_image = mono_image_open_from_data();
	//void *image = mono_assembly_get_image(assembly);
	//void *class = mono_class_from_name(image, namespace, classname);
	//void *method = mono_class_get_method_from_name();
	//mono_runtime_invoke()
}	
