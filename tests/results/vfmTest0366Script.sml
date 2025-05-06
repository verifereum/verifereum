open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0366Theory;
val () = new_theory "vfmTest0366";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0366") $ get_result_defs "vfmTestDefs0366";
val () = export_theory_no_docs ();
