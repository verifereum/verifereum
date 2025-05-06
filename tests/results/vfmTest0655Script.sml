open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0655Theory;
val () = new_theory "vfmTest0655";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0655") $ get_result_defs "vfmTestDefs0655";
val () = export_theory_no_docs ();
