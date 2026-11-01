Theory vfmTestDefs3038[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip6110_deposits/modified_contract/invalid_layout.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip6110_deposits/modified_contract/invalid_layout.json");
val defs = mapi (define_test "3038") tests;
