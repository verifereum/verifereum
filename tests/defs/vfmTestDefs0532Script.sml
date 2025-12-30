Theory vfmTestDefs0532[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBadOpcode/undefinedOpcodeFirstByte.json";
val defs = mapi (define_test "0532") tests;
