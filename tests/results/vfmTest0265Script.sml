open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0265Theory;
val () = new_theory "vfmTest0265";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0265") $ get_result_defs "vfmTestDefs0265";
val () = export_theory_no_docs ();
