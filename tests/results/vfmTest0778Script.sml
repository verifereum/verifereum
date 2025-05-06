open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0778Theory;
val () = new_theory "vfmTest0778";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0778") $ get_result_defs "vfmTestDefs0778";
val () = export_theory_no_docs ();
