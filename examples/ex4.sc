private uint32 count(private uint32[] data, private uint32 value) {
    public uint32 n; n = vecLength(data);
    private bool[n] matches = (data == value);
    private uint32 counter; counter = vecSum(matches);
    return counter;
}