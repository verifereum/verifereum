Theory vfmTestDefs0340[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7954_increase_max_contract_size/max_code_size/max_code_size_linear_execution.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7954_increase_max_contract_size/max_code_size/max_code_size_linear_execution.json");
val defs = mapi (define_test "0340") tests;
