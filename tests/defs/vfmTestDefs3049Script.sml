Theory vfmTestDefs3049[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip7251_consolidations/modified_consolidation_contract/extra_consolidations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip7251_consolidations/modified_consolidation_contract/extra_consolidations.json");
val defs = mapi (define_test "3049") tests;
