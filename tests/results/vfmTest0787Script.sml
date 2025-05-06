open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0787Theory;
val () = new_theory "vfmTest0787";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0787") $ get_result_defs "vfmTestDefs0787";
val () = export_theory_no_docs ();
