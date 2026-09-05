Theory vfmTestDefs0735[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1559/out_of_funds_old_types/out_of_funds_old_types.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1559/out_of_funds_old_types/out_of_funds_old_types.json");
val defs = mapi (define_test "0735") tests;
