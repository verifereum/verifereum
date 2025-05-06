open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0473Theory;
val () = new_theory "vfmTest0473";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0473") $ get_result_defs "vfmTestDefs0473";
val () = export_theory_no_docs ();
