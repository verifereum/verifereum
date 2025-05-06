open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0048Theory;
val () = new_theory "vfmTest0048";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0048") $ get_result_defs "vfmTestDefs0048";
val () = export_theory_no_docs ();
