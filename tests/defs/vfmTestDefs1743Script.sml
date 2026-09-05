Theory vfmTestDefs1743[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSolidityTest/call_low_level_creates_solidity/call_low_level_creates_solidity.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSolidityTest/call_low_level_creates_solidity/call_low_level_creates_solidity.json");
val defs = mapi (define_test "1743") tests;
