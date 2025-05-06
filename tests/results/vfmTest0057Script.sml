open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0057Theory;
val () = new_theory "vfmTest0057";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0057") $ get_result_defs "vfmTestDefs0057";
val () = export_theory_no_docs ();
