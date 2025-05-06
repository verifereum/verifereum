open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0734Theory;
val () = new_theory "vfmTest0734";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0734") $ get_result_defs "vfmTestDefs0734";
val () = export_theory_no_docs ();
