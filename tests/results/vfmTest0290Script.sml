open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0290Theory;
val () = new_theory "vfmTest0290";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0290") $ get_result_defs "vfmTestDefs0290";
val () = export_theory_no_docs ();
