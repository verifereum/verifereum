Theory vfmTestDefs0376[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/access_list_cost/access_list_surcharge_with_recipient_costs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/access_list_cost/access_list_surcharge_with_recipient_costs.json");
val defs = mapi (define_test "0376") tests;
