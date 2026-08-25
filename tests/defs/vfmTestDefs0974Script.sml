Theory vfmTestDefs0974[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/EXTCODESIZE_toNonExistent.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP158Specific/EXTCODESIZE_toNonExistent.json");
val defs = mapi (define_test "0974") tests;
