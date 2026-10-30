Theory vfmTestDefs0356[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/additional_coverage/floor_cost_not_reduced_by_refunds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/additional_coverage/floor_cost_not_reduced_by_refunds.json");
val defs = mapi (define_test "0356") tests;
