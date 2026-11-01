Theory vfmTestDefs0846[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8246_selfdestruct_no_burn/selfdestruct_no_burn/selfdestructing_initcode_preserves_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8246_selfdestruct_no_burn/selfdestruct_no_burn/selfdestructing_initcode_preserves_balance.json");
val defs = mapi (define_test "0846") tests;
