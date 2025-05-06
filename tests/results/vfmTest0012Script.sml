open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0012Theory;
val () = new_theory "vfmTest0012";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0012") $ get_result_defs "vfmTestDefs0012";
val () = export_theory_no_docs ();
