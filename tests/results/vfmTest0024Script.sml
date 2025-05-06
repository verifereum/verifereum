open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0024Theory;
val () = new_theory "vfmTest0024";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0024") $ get_result_defs "vfmTestDefs0024";
val () = export_theory_no_docs ();
