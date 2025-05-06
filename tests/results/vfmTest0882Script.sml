open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0882Theory;
val () = new_theory "vfmTest0882";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0882") $ get_result_defs "vfmTestDefs0882";
val () = export_theory_no_docs ();
