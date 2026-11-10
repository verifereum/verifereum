Theory vfmTestDefs1489[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP2930/storage_costs/storage_costs.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP2930/storage_costs/storage_costs.json");
val defs = mapi (define_test "1489") tests;
