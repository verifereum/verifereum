Theory vfmTestDefs0799[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCreate2/Create2OOGafterInitCodeRevert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCreate2/Create2OOGafterInitCodeRevert.json");
val defs = mapi (define_test "0799") tests;
