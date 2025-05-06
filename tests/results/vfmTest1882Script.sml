open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1882Theory;
val () = new_theory "vfmTest1882";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1882") $ get_result_defs "vfmTestDefs1882";
val () = export_theory_no_docs ();
