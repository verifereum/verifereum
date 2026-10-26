Theory vfmTestDefs0366[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/floor_boundary_exact_balance/below_amsterdam_floor_with_exact_balance_sender.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/floor_boundary_exact_balance/below_amsterdam_floor_with_exact_balance_sender.json");
val defs = mapi (define_test "0366") tests;
