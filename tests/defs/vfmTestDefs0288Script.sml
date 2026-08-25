Theory vfmTestDefs0288[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_eip_7623.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7623_increase_calldata_cost/test_eip_7623.json");
val defs = mapi (define_test "0288") tests;
