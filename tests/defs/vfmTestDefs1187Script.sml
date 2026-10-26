Theory vfmTestDefs1187[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/osaka/eip7918_blob_reserve_price/blob_base_fee/reserve_price_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/osaka/eip7918_blob_reserve_price/blob_base_fee/reserve_price_boundary.json");
val defs = mapi (define_test "1187") tests;
