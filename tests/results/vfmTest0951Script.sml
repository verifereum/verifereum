open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0951Theory;
val () = new_theory "vfmTest0951";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0951") $ get_result_defs "vfmTestDefs0951";
val () = export_theory_no_docs ();
