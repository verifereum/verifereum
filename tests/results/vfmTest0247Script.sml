open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0247Theory;
val () = new_theory "vfmTest0247";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0247") $ get_result_defs "vfmTestDefs0247";
val () = export_theory_no_docs ();
