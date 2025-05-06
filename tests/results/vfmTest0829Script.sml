open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0829Theory;
val () = new_theory "vfmTest0829";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0829") $ get_result_defs "vfmTestDefs0829";
val () = export_theory_no_docs ();
