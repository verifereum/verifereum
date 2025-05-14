open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0030";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/beacon_root_contract/calldata_lengths.json";
val defs = mapi (define_test "0030") tests;
val () = export_theory_no_docs ();
