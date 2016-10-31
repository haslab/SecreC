#!/usr/bin/env python
import struct
import sys

class IncompleteInput(Exception):
    pass

def parseArguments(inFile=sys.stdin, sizeTypeFormat='Q', sizeTypeSize=8,
        encoding='utf-8'):
    def readBlock(size):
        buf = inFile.buffer.read(size) if hasattr(inFile, 'buffer') else inFile.read(size)
        if len(buf) != size:
            raise IncompleteInput()
        return buf

    def readString(size):
        return readBlock(size).decode(encoding)

    def parseData(typeName, data):
        if typeName == 'bool':
            return list(struct.unpack('%s?' % len(data), data))
        elif typeName == 'float32':
            return list(struct.unpack('%sf' % (len(data) // 4), data))
        elif typeName == 'float64':
            return list(struct.unpack('%sd' % (len(data) // 8), data))
        elif typeName == 'int8':
            return list(struct.unpack('%sb' % len(data), data))
        elif typeName == 'int16':
            return list(struct.unpack('%sh' % (len(data) // 2), data))
        elif typeName == 'int32':
            return list(struct.unpack('%sl' % (len(data) // 4), data))
        elif typeName == 'int64':
            return list(struct.unpack('%sq' % (len(data) // 8), data))
        elif typeName == 'uint8':
            return list(struct.unpack('%sB' % len(data), data))
        elif typeName == 'uint16':
            return list(struct.unpack('%sH' % (len(data) // 2), data))
        elif typeName == 'uint32':
            return list(struct.unpack('%sL' % (len(data) // 4), data))
        elif typeName == 'uint64':
            return list(struct.unpack('%sQ' % (len(data) // 8), data))
        elif typeName == 'string':
            return data.decode(encoding)
        else:
            return data

    args = {}

    try:
        while True:
            argNameSize = struct.unpack(sizeTypeFormat, readBlock(sizeTypeSize))[0]
            argName = readString(argNameSize)
            pdNameSize = struct.unpack(sizeTypeFormat, readBlock(sizeTypeSize))[0]
            pdName = readString(pdNameSize)
            typeNameSize = struct.unpack(sizeTypeFormat, readBlock(sizeTypeSize))[0]
            typeName = readString(typeNameSize)
            argDataSize = struct.unpack(sizeTypeFormat, readBlock(sizeTypeSize))[0]
            argData = parseData(typeName, readBlock(argDataSize))
            args[argName] = argData
    except IncompleteInput:
        pass

    return args

def main():
    try:
        args = parseArguments()

        if not 'test_count' in args or not len(args['test_count']):
            raise Exception('Missing "test_count" result value!')

        if not 'passed_count' in args or not len(args['passed_count']):
            raise Exception('Missing "passed_count" result value!')

        testCount = args['test_count'][0]
        passedCount = args['test_count'][0]

        for i in range(testCount):
            descLabel = 'test%s_description' % i
            resLabel = 'test%s_result' % i

            if not descLabel in args:
                raise Exception('Missing "{}" result value!'.format(descLabel))

            if not resLabel in args or not len(args[resLabel]):
                raise Exception('Missing "{}" result value!'.format(resLabel))

            desc = args[descLabel]
            res = args[resLabel][0]

            if res:
                sys.stdout.write('{} - PASSED\n'.format(desc))
            else:
                sys.stderr.write('{} - FAILED\n'.format(desc))

        sys.stdout.write('Passed: {}, Failed: {}, Total: {}\n'.format(passedCount, testCount - passedCount, testCount))
    except Exception as e:
        sys.stderr.write('Error: {}\n'.format(e.__str__()))
        sys.exit(1)

if __name__ == "__main__":
    main()
