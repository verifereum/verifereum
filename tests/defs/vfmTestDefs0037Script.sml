Theory vfmTestDefs0037[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/create/create_oog_from_eoa_refunds/create_oog_from_eoa_refunds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/create/create_oog_from_eoa_refunds/create_oog_from_eoa_refunds.json");
val defs = mapi (define_test "0037") tests;
