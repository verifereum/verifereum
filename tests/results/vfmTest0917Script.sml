open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0917Theory;
val () = new_theory "vfmTest0917";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0917") $ get_result_defs "vfmTestDefs0917";
val () = export_theory_no_docs ();
