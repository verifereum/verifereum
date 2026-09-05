Theory vfmTestDefs2063[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/callcode_to_return1/callcode_to_return1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/callcode_to_return1/callcode_to_return1.json");
val defs = mapi (define_test "2063") tests;
