Theory vfmTestDefs0973[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/EXTCODESIZE_toEpmtyParis.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP158Specific/EXTCODESIZE_toEpmtyParis.json");
val defs = mapi (define_test "0973") tests;
