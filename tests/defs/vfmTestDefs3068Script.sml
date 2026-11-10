Theory vfmTestDefs3068[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/gas/self_set_code_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/gas/self_set_code_cost.json");
val defs = mapi (define_test "3068") tests;
