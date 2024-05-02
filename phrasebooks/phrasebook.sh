### set verbosity
set -x # short for `set -o xtrace` see `man bash` for '-o option-name'
echo "HI"
set +x to turn it off

### find directories, execute something ({} is variable, + is terminator)
find /path/to/base/dir -type d -exec chmod 755 {} +
find /path/to/base/dir -type f -exec chmod 755 {} +

echo "Here are the other files starting with SNIP"
for file in snip*; do
	[ -e "$file" ] || continue
	echo "file is: $file"
done

echo "Here are the other files starting with SNIP"
for file in snip*; do [ -e "$file" ] || continue; echo "file is: $file"; done

# functions
myfunc # calls myfunc()
myfunc "hi" # calls myfunc("hi"), and myfunc() sees it in $1

## return value method1: global variable
function foo()
{
	g_result='bar'
}

foo
echo $g_result
## return value method2: command substitution
function foo()
{
	local result='bar'
	echo "my irrelevant info" >&2 # not captured, sent to stderr
	echo "$result"
}

result=$(foo)
echo $result
## return value method3: out variable
function foo()
{
	local __outvar=$1
	local result='bar'
	eval $__outvar="'$result'"
}

foo result
echo $result

### call command 10 times
for i in {1..10}; do ./test.py; done
### call command for all found files
for fpath in ./linux/typelib_bntls_sk/*.bntl; do ./addaltnames.py "$fpath"; done
### call command for all found files, recursively
find /path/to -name "*.bntl" | xargs -L 1 ./imposetypes.py

### do files or directories exist?
if [ -f "/etc/passwd" ]; then echo "The file exists"; fi
if ! [[ -f "/etc/passwd" ]]; then echo "The doesn't exist."; fi
if [ ! -f "/etc/passwd" ]; then echo "The doesn't exist."; fi
if [ -d "/etc/" ]; then echo "The directory exists"; fi

### functions
# $1 is positional parameter
# $@ is array-like construct of all positional parameters
# https://www.gnu.org/software/bash/manual/html_node/Shell-Variables.html
command ls # does ls without using alias
echo $'\x41' # print 'A' coolness, see man bash page under QUOTING

## misc

export PS1="$ " # anonymize prompt
set -e # exit when any command fails

# get type of command (alias, function, builtin, file, keyword)
type -t <command>
