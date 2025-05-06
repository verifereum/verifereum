open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0381Theory;
val () = new_theory "vfmTest0381";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0381") $ get_result_defs "vfmTestDefs0381";
val () = export_theory_no_docs ();
