Theory vfmTestDefs0385[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/floor_boundary_exact_balance/access_list_floor_with_exact_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/floor_boundary_exact_balance/access_list_floor_with_exact_balance.json");
val defs = mapi (define_test "0385") tests;
