open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0031";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4788_beacon_root/beacon_root_contract/invalid_beacon_root_calldata_value.json";
val defs = mapi (define_test "0031") tests;
val () = export_theory_no_docs ();
