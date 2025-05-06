open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1646Theory;
val () = new_theory "vfmTest1646";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1646") $ get_result_defs "vfmTestDefs1646";
val () = export_theory_no_docs ();
