open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0892Theory;
val () = new_theory "vfmTest0892";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0892") $ get_result_defs "vfmTestDefs0892";
val () = export_theory_no_docs ();
