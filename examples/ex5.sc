
string argument (string name) {
    uint num_bytes;
    __syscall("Process_argument", __cref name, __return num_bytes);
    uint8[[1]] bytes (num_bytes);
    if (num_bytes > 0)
        __syscall("Process_argument", __cref name, __ref bytes, __return num_bytes);
        return __string_from_bytes (bytes);
    return;
}