# Summary of Uncheckable Files
Summary of results for proof files which the checker isn't able to check.
| Description                                | # Files | Search String           |
|--------------------------------------------|---------|-------------------------|
| `get_clause` can't find clause at ID       | 8       | "VeritSyntax.mk_clause" |
| `findi` can't find an element              | 2       | "findi"                 |
| `get_eq` expects atomic equality           | 2       | "get_eq"                |
| Invalid character '.'                      | 366     | "Invalid character '.'" |
| Invalid character '-'	                     | 18	   | Invalid character '-'   |
| Invalid character '$'	                     | 74	   | Invalid character '$'   |
| VeritParser.Error	                         | 3923	   | VeritParser.Error       |
| process_subproof failed	                 | 2166	   | process_subproof: failed|
| process_cong failed	                     | 553	   | process_cong:           |
| process_trans failed	                     | 358	   | process_trans:    |
|Number of files checker isn't able to check | 7468    |                         |

Each of the folders in this (`QFUFTests`) directory represents one of these errors and contains 2-3 benchmarks for which the checker fails.