open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0390Theory;
val () = new_theory "vfmTest0390";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0390") $ get_result_defs "vfmTestDefs0390";
val () = export_theory_no_docs ();
