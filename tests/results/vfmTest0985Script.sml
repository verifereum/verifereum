open HolKernel wordsLib vfmTestResultLib vfmTestDefs0985Theory;
val () = new_theory "vfmTest0985";
val thyn = "vfmTestDefs0985";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
val () = vfmTestAuxLib.export_theory_no_docs ();
