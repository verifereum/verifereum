open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0288Theory;
val () = new_theory "vfmTest0288";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0288") $ get_result_defs "vfmTestDefs0288";
val () = export_theory_no_docs ();
