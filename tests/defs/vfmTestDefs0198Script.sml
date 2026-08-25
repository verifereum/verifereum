Theory vfmTestDefs0198[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7918_blob_reserve_price/test_reserve_price_at_transition.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7918_blob_reserve_price/test_reserve_price_at_transition.json");
val defs = mapi (define_test "0198") tests;
