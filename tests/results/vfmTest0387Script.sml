open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0387Theory;
val () = new_theory "vfmTest0387";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0387") $ get_result_defs "vfmTestDefs0387";
val () = export_theory_no_docs ();
