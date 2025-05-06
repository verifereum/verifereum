open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1148Theory;
val () = new_theory "vfmTest1148";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1148") $ get_result_defs "vfmTestDefs1148";
val () = export_theory_no_docs ();
