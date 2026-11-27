import java.nio.file.Path;

import org.apache.parquet.column.ParquetProperties.WriterVersion;
import org.apache.parquet.conf.PlainParquetConfiguration;
import org.apache.parquet.example.data.simple.SimpleGroupFactory;
import org.apache.parquet.hadoop.example.ExampleParquetWriter;
import org.apache.parquet.hadoop.metadata.CompressionCodecName;
import org.apache.parquet.io.LocalOutputFile;
import org.apache.parquet.schema.MessageTypeParser;

/** Produce original Snappy PARQUET_1_0 TIMESTAMP dictionary frames using parquet-java 1.16.0. */
class Write {
    private static final long[] UTC_TICKS = {Long.MIN_VALUE, -1001, 0, Long.MAX_VALUE, -1001};
    private static final long[] LOCAL_TICKS = {Long.MIN_VALUE, -1001, 0, -1001, 0};

    private static void write(Path directory, boolean optional) throws Exception {
        var name = optional ? "local_micros" : "utc_nanos";
        var schema = MessageTypeParser.parseMessageType(optional
                ? "message timestamps { optional int64 ticks (TIMESTAMP(MICROS,false)); }"
                : "message timestamps { required int64 ticks (TIMESTAMP(NANOS,true)); }");
        var factory = new SimpleGroupFactory(schema);
        var ticks = optional ? LOCAL_TICKS : UTC_TICKS;
        try (var writer = ExampleParquetWriter.builder(new LocalOutputFile(directory.resolve(name + ".parquet")))
                .withConf(new PlainParquetConfiguration())
                .withType(schema)
                .withWriterVersion(WriterVersion.PARQUET_1_0)
                .withDictionaryEncoding(true)
                .withDictionaryPageSize(1024)
                .withCompressionCodec(CompressionCodecName.SNAPPY)
                .withPageWriteChecksumEnabled(true)
                .withPageRowCountLimit(48)
                .withRowGroupSize(2048L)
                .build()) {
            for (int i = 0; i < 4096; i++) {
                var row = factory.newGroup();
                if (!optional || i % 7 != 0) {
                    row.append("ticks", ticks[i % ticks.length]);
                }
                writer.write(row);
            }
        }
    }

    public static void main(String[] args) throws Exception {
        var directory = Path.of(args[0]);
        write(directory, true);
        write(directory, false);
    }
}
