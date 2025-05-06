open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1722Theory;
val () = new_theory "vfmTest1722";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1722") $ get_result_defs "vfmTestDefs1722";
val () = export_theory_no_docs ();
