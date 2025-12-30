Theory vfmTestDefs0999[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/callToNonExistent.json";
val defs = mapi (define_test "0999") tests;
