Theory vfmTestDefs0531[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stBadOpcode/operationDiffGas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stBadOpcode/operationDiffGas.json");
val defs = mapi (define_test "0531") tests;
