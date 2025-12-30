Theory vfmTestDefs2398[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorAddressTooBigLeft.json";
val defs = mapi (define_test "2398") tests;
