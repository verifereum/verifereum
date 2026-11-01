Theory vfmTestDefs1468[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP1559/low_fee_cap/low_fee_cap.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP1559/low_fee_cap/low_fee_cap.json");
val defs = mapi (define_test "1468") tests;
