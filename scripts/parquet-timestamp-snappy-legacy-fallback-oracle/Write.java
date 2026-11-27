import java.nio.file.Path;

import org.apache.parquet.column.ParquetProperties.WriterVersion;
import org.apache.parquet.conf.PlainParquetConfiguration;
import org.apache.parquet.example.data.simple.SimpleGroupFactory;
import org.apache.parquet.hadoop.example.ExampleParquetWriter;
import org.apache.parquet.hadoop.metadata.CompressionCodecName;
import org.apache.parquet.io.LocalOutputFile;
import org.apache.parquet.schema.MessageTypeParser;

/** Produce a complete Snappy V1 file with genuine parquet-java dictionary fallback. */
class Write {
    private static final int ROWS = 384;
    private static final long[] REPEATED = {Long.MIN_VALUE, -1001, 0, Long.MAX_VALUE};

    public static void main(String[] args) throws Exception {
        var schema = MessageTypeParser.parseMessageType("""
                message timestamps {
                  optional int64 local_ticks (TIMESTAMP(MICROS,false));
                  required int64 utc_ticks (TIMESTAMP(NANOS,true));
                }
                """);
        var factory = new SimpleGroupFactory(schema);
        var path = Path.of(args[0], "fallback.parquet");
        try (var writer = ExampleParquetWriter.builder(new LocalOutputFile(path))
                .withConf(new PlainParquetConfiguration())
                .withType(schema)
                .withWriterVersion(WriterVersion.PARQUET_1_0)
                .withDictionaryEncoding(true)
                .withDictionaryPageSize(96)
                .withCompressionCodec(CompressionCodecName.SNAPPY)
                .withPageWriteChecksumEnabled(true)
                .withPageRowCountLimit(32)
                .withRowGroupRowCountLimit(ROWS)
                .build()) {
            for (int group = 0; group < 2; group++) {
                for (int slot = 0; slot < ROWS; slot++) {
                    long local = 224 <= slot && slot < 320
                            ? -1_000_000L * (group + 1) + 113L * slot
                            : REPEATED[slot % REPEATED.length] ^ group;
                    long utc = ~local;
                    var row = factory.newGroup().append("utc_ticks", utc);
                    if ((slot + group) % 13 != 5) {
                        row.append("local_ticks", local);
                    }
                    writer.write(row);
                }
            }
        }
    }
}
