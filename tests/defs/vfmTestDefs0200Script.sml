Theory vfmTestDefs0200[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_reserve_price_various_base_fee_scenarios.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7918_blob_reserve_price/test_reserve_price_various_base_fee_scenarios.json");
val defs = mapi (define_test "0200") tests;
