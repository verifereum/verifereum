open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0608Theory;
val () = new_theory "vfmTest0608";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0608") $ get_result_defs "vfmTestDefs0608";
val () = export_theory_no_docs ();
