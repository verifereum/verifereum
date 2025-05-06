open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0585Theory;
val () = new_theory "vfmTest0585";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0585") $ get_result_defs "vfmTestDefs0585";
val () = export_theory_no_docs ();
