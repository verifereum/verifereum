Theory vfmTestDefs0345[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7954_increase_max_contract_size/max_code_size/max_code_size_with_max_initcode_via_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7954_increase_max_contract_size/max_code_size/max_code_size_with_max_initcode_via_create.json");
val defs = mapi (define_test "0345") tests;
