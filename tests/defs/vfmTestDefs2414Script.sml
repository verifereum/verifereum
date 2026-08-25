Theory vfmTestDefs2414[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/TestNameRegistrator.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSystemOperationsTest/TestNameRegistrator.json");
val defs = mapi (define_test "2414") tests;
