open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0325Theory;
val () = new_theory "vfmTest0325";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0325") $ get_result_defs "vfmTestDefs0325";
val () = export_theory_no_docs ();
