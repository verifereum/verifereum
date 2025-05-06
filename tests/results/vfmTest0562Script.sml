open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0562Theory;
val () = new_theory "vfmTest0562";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0562") $ get_result_defs "vfmTestDefs0562";
val () = export_theory_no_docs ();
