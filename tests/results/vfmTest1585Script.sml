open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1585Theory;
val () = new_theory "vfmTest1585";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1585") $ get_result_defs "vfmTestDefs1585";
val () = export_theory_no_docs ();
