open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0798Theory;
val () = new_theory "vfmTest0798";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0798") $ get_result_defs "vfmTestDefs0798";
val () = export_theory_no_docs ();
