Theory vfmTestDefs0801[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCreate2/Create2OnDepth1023.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCreate2/Create2OnDepth1023.json");
val defs = mapi (define_test "0801") tests;
