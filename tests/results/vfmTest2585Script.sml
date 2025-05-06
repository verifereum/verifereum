open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2585Theory;
val () = new_theory "vfmTest2585";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2585") $ get_result_defs "vfmTestDefs2585";
val () = export_theory_no_docs ();
