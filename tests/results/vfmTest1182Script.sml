open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1182Theory;
val () = new_theory "vfmTest1182";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1182") $ get_result_defs "vfmTestDefs1182";
val () = export_theory_no_docs ();
