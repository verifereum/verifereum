open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0029";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/beacon_root_contract/beacon_root_transition.json";
val defs = mapi (define_test "0029") tests;
val () = export_theory_no_docs ();
