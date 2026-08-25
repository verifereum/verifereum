Theory vfmTestDefs0459[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/jumpi.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/jumpi.json");
val defs = mapi (define_test "0459") tests;
