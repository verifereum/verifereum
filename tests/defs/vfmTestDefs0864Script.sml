Theory vfmTestDefs0864[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCodeRevert.json";
val defs = mapi (define_test "0864") tests;
