Theory vfmTestDefs2113[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/point_at_infinity_ec_recover/point_at_infinity_ec_recover.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/point_at_infinity_ec_recover/point_at_infinity_ec_recover.json");
val defs = mapi (define_test "2113") tests;
