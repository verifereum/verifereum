Theory vfmTestDefs2259[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/vmIOandFlowOperations/sstore_sload/sstore_sload.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/vmIOandFlowOperations/sstore_sload/sstore_sload.json");
val defs = mapi (define_test "2259") tests;
