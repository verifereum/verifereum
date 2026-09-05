Theory vfmTestDefs0456[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_fail_balance_too_low/create_fail_balance_too_low.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCreateCallCodeTest/create_fail_balance_too_low/create_fail_balance_too_low.json");
val defs = mapi (define_test "0456") tests;
