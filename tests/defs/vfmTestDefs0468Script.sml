Theory vfmTestDefs0468[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/VMTests/vmIOandFlowOperations/return.json");
val defs = mapi (define_test "0468") tests;
