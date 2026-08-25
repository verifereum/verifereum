Theory vfmTest0566[no_sig_docs]
Ancestors vfmTestDefs0566
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0566_0.nsv"];
val thyn = "vfmTestDefs0566";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
