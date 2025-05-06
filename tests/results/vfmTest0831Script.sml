open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0831Theory;
val () = new_theory "vfmTest0831";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0831") $ get_result_defs "vfmTestDefs0831";
val () = export_theory_no_docs ();
