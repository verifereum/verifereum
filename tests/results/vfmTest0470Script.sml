open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0470Theory;
val () = new_theory "vfmTest0470";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0470") $ get_result_defs "vfmTestDefs0470";
val () = export_theory_no_docs ();
