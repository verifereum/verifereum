Theory vfmTestDefs0129[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/test_call_memory_expands_on_early_revert.json";
val defs = mapi (define_test "0129") tests;
