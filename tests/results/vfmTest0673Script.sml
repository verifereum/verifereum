open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0673Theory;
val () = new_theory "vfmTest0673";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0673") $ get_result_defs "vfmTestDefs0673";
val () = export_theory_no_docs ();
