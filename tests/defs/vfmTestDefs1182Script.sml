Theory vfmTestDefs1182[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/osaka/eip7883_modexp_gas_increase/modexp_thresholds/modexp_used_in_transaction_entry_points.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/osaka/eip7883_modexp_gas_increase/modexp_thresholds/modexp_used_in_transaction_entry_points.json");
val defs = mapi (define_test "1182") tests;
