Theory vfmTestDefs1994[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_changeFromExternalCallInInitCode.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSStoreTest/sstore_changeFromExternalCallInInitCode.json");
val defs = mapi (define_test "1994") tests;
