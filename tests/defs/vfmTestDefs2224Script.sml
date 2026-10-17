Theory vfmTestDefs2224[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/vmIOandFlowOperations/jump/jump.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/vmIOandFlowOperations/jump/jump.json");
val defs = mapi (define_test "2224") tests;
