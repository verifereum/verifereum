open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0032";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/test_beacon_root_contract_timestamps.json";
val defs = mapi (define_test "0032") tests;
val () = export_theory_no_docs ();
