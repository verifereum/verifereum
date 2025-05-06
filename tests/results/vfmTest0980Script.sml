open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0980Theory;
val () = new_theory "vfmTest0980";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0980") $ get_result_defs "vfmTestDefs0980";
val () = export_theory_no_docs ();
