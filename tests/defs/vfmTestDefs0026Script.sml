open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0026";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_contract_timestamps.json";
val defs = mapi (define_test "0026") tests;
val () = export_theory_no_docs ();
