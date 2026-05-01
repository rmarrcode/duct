using System.Collections;
using System.Runtime.CompilerServices;
using System.Numerics;
using System.Net.Sockets;
using System.Reflection;
using System.Text.Json;
using Dafny;
using Npgsql;

public static class DuctDbBridge
{
    private static string? s_connectionString;

    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = false
    };
    private static readonly object SyncLock = new();
    private static readonly ConditionalWeakTable<DB.Database, SyncState> SyncStates = new();

    private sealed class SyncState
    {
        public int SyncedCount { get; set; }
    }

    public static void Configure(string connectionString)
    {
        s_connectionString = string.IsNullOrWhiteSpace(connectionString)
            ? throw new ArgumentException("Connection string must not be empty.", nameof(connectionString))
            : connectionString;
    }

    public static void ExecuteProgram(DB.Database? db, DB._IDbProgram? program)
    {
        if (db is null || program is null)
        {
            return;
        }

        lock (SyncLock)
        {
            Dafny.ISequence<DB._IDbValue> entries =
                DB.__default.ExecuteOperations(Dafny.Sequence<DB._IDbValue>.Empty, db.operations);
            Dafny.ISequence<DB._IDbChange> changes = DB.__default.ProgramOperations(entries, program);

            db.ApplyOperations(changes);
            PersistUnsyncedOperations(db);
        }
    }

    public static void PersistDatabase(DB.Database? db)
    {
        if (db is null)
        {
            return;
        }

        lock (SyncLock)
        {
            PersistUnsyncedOperations(db);
        }
    }

    private static void PersistUnsyncedOperations(DB.Database db)
    {
        SyncState state = SyncStates.GetOrCreateValue(db);
        int totalOperations = db.operations.Count;
        int syncedCount = state.SyncedCount;

        for (int i = state.SyncedCount; i < totalOperations; i++)
        {
            try
            {
                Persist(db, db.operations.Select(new BigInteger(i)));
                syncedCount++;
            }
            catch (NpgsqlException ex) when (ex.InnerException is SocketException)
            {
                Console.Error.WriteLine(
                    $"Duct DB persistence unavailable; {totalOperations - i} operation(s) remain queued. {ex.Message}");
                break;
            }
        }

        state.SyncedCount = syncedCount;
    }

    public static void Persist(object db, object value)
    {
        EnsureSchema();

        string rootKind = value.GetType().FullName ?? value.GetType().Name;
        string payloadJson = JsonSerializer.Serialize(ToPlainObject(value), JsonOptions);

        using var connection = new NpgsqlConnection(GetConnectionString());
        connection.Open();

        using var command = connection.CreateCommand();
        command.CommandText = @"
insert into dafny_objects(root_kind, payload_json)
values ($root_kind, $payload_json);";
        command.Parameters.AddWithValue("$root_kind", rootKind);
        command.Parameters.AddWithValue("$payload_json", payloadJson);
        command.ExecuteNonQuery();
    }

    private static object? ToPlainObject(object? value)
    {
        if (value is null)
        {
            return null;
        }

        if (value is string s)
        {
            return s;
        }

        if (value is bool or byte or sbyte or short or ushort or int or uint or long or ulong or float or double or decimal)
        {
            return value;
        }

        if (value is BigInteger big)
        {
            return big.ToString();
        }

        if (value is IEnumerable<Rune> runes)
        {
            return string.Concat(runes.Select(r => char.ConvertFromUtf32(r.Value)));
        }

        if (value is IDictionary dictionary)
        {
            var mapped = new Dictionary<string, object?>();
            foreach (DictionaryEntry entry in dictionary)
            {
                string key = entry.Key?.ToString() ?? "null";
                mapped[key] = ToPlainObject(entry.Value);
            }
            return mapped;
        }

        if (value is IEnumerable enumerable)
        {
            var items = new List<object?>();
            foreach (var item in enumerable)
            {
                items.Add(ToPlainObject(item));
            }
            return items;
        }

        PropertyInfo[] props = value.GetType()
            .GetProperties(BindingFlags.Public | BindingFlags.Instance)
            .Where(p => p.CanRead && p.GetIndexParameters().Length == 0 && p.Name.StartsWith("dtor_", StringComparison.Ordinal))
            .ToArray();

        if (props.Length == 0)
        {
            return value.ToString();
        }

        var result = new Dictionary<string, object?>();
        result["__type"] = value.GetType().FullName ?? value.GetType().Name;

        foreach (PropertyInfo prop in props)
        {
            result[NormalizePropertyName(prop.Name)] = ToPlainObject(prop.GetValue(value));
        }

        return result;
    }

    private static string NormalizePropertyName(string propertyName)
    {
        string name = propertyName["dtor_".Length..];
        return name.Replace("__", "_");
    }

    private static void EnsureSchema()
    {
        using var connection = new NpgsqlConnection(GetConnectionString());
        connection.Open();

        using var command = connection.CreateCommand();
        command.CommandText = @"
create table if not exists dafny_objects (
  id bigint generated by default as identity primary key,
  root_kind text not null,
  payload_json text not null,
  created_at timestamptz not null default current_timestamp
);";
        command.ExecuteNonQuery();
    }

    private static string GetConnectionString() =>
        s_connectionString
        ?? throw new InvalidOperationException("DuctDbBridge has not been configured.");
}
