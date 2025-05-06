open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1290Theory;
val () = new_theory "vfmTest1290";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1290") $ get_result_defs "vfmTestDefs1290";
val () = export_theory_no_docs ();
