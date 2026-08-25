Theory vfmTestDefs2431[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorZeroMemExpansion.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorZeroMemExpansion.json");
val defs = mapi (define_test "2431") tests;
