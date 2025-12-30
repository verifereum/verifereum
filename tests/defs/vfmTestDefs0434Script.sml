Theory vfmTestDefs0434[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmArithmeticTest/fib.json";
val defs = mapi (define_test "0434") tests;
