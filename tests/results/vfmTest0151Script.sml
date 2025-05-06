open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0151Theory;
val () = new_theory "vfmTest0151";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0151") $ get_result_defs "vfmTestDefs0151";
val () = export_theory_no_docs ();
