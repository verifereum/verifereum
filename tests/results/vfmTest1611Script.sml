open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1611Theory;
val () = new_theory "vfmTest1611";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1611") $ get_result_defs "vfmTestDefs1611";
val () = export_theory_no_docs ();
