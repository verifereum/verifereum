Theory vfmTestDefs0892[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/deleagateCallAfterValueTransfer.json";
val defs = mapi (define_test "0892") tests;
