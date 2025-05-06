open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1687Theory;
val () = new_theory "vfmTest1687";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1687") $ get_result_defs "vfmTestDefs1687";
val () = export_theory_no_docs ();
