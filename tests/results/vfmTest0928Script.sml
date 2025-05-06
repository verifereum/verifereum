open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0928Theory;
val () = new_theory "vfmTest0928";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0928") $ get_result_defs "vfmTestDefs0928";
val () = export_theory_no_docs ();
