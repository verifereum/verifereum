open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0229Theory;
val () = new_theory "vfmTest0229";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0229") $ get_result_defs "vfmTestDefs0229";
val () = export_theory_no_docs ();
