open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0038";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_multi_block_beacon_root_timestamp_calls.json";
val defs = mapi (define_test "0038") tests;
val () = export_theory_no_docs ();
