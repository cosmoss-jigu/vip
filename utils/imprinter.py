#!/usr/bin/env python3

# refer to these two sources:
# https://en.wikipedia.org/wiki/Executable_and_Linkable_Format
# http://man7.org/linux/man-pages/man5/elf.5.html

import os, argparse

def imprint(filepath):
    with open(filepath, 'rb+') as f:
        f.seek(4)
        ei_class = f.read(1)

        if (ei_class == b'\x01'):
            f.seek(36) # is 32-bit formatted 
        else:
            f.seek(48) # is 64--bit formatted

        # imprint the e_flags: unused 4 bytes long
        f.write(b'\xBE') 
        
        f.close()

def is_imprinted(filepath):
    with open(filepath, 'rb+') as f:
        f.seek(4)
        ei_class = f.read(1)

        if (ei_class == b'\x01'):
            f.seek(36) # is 32-bit formatted
        else:
            f.seek(48) # is 64-bit formatted
        
        byte = f.read(1);
        
        f.close()

        return (byte == b'\xBE')
        
        
def is_convertable(filepath):
    with open(filepath, 'rb') as f:
        s = f.read(4)
        if s != b'\x7fELF':
            f.close()
            return False
        f.close()
        return True

def get_files(filename, dirname, rdirname):
    blacklist = ["src", "data", "Docs", "Spec"]
    if filename:
        if os.path.isfile(filename):
            fn = filename
            if is_convertable(fn):
                yield(fn)
    if dirname:
        for f in os.listdir(dirname) and f not in blacklist:
            fn = os.path.join(dirname, f)
            if os.path.isfile(fn) and is_convertable(fn):
                yield(fn)
    if rdirname:
        for root, dirs, files in os.walk(rdirname):
            for f in files:
                fn = os.path.join(root, f)
                if is_convertable(fn):
                    yield(fn)

def main():
    # parse option
    parser = argparse.ArgumentParser()
    parser.add_argument("-f", dest='m_file', help="Convert a single file")
    parser.add_argument('-d', dest='m_dir',  help="Convert all files in the directory")
    parser.add_argument('-r', dest='m_rdir', help="Recursively convert all files in the directory")
    parser.add_argument('-c', action="store_true", help="Check if file is imprinted or not")
    args = parser.parse_args()

    # check if args are same
    if args.m_file == None and args.m_dir == None and args.m_rdir == None:
        parser.print_help()
        exit(1)

    # imprint files ingiven pathes
    for fn in get_files(args.m_file, args.m_dir, args.m_rdir):
        if (args.c):
            if (is_imprinted(fn)):
                print(" [*] " + fn + " is Imprinted")
            else:
                print(" [X] " + fn + " is NOT Imprinted")
        else:
            print("# Imprinting: " + fn)
            imprint(fn);

if __name__=="__main__":
    main()
