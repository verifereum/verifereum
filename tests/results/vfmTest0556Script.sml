open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0556Theory;
val () = new_theory "vfmTest0556";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0556") $ get_result_defs "vfmTestDefs0556";
val () = export_theory_no_docs ();
