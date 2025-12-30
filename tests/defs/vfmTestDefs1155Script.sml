Theory vfmTestDefs1155[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/codeCopyOffset.json";
val defs = mapi (define_test "1155") tests;
