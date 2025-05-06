open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1750Theory;
val () = new_theory "vfmTest1750";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1750") $ get_result_defs "vfmTestDefs1750";
val () = export_theory_no_docs ();
