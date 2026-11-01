Theory vfmTestDefs3050[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip7251_consolidations/modified_consolidation_contract/system_contract_errors.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip7251_consolidations/modified_consolidation_contract/system_contract_errors.json");
val defs = mapi (define_test "3050") tests;
