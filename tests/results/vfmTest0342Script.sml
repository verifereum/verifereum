Theory vfmTest0342[no_sig_docs]
Ancestors vfmTestDefs0342
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0342_0.nsv"];
val thyn = "vfmTestDefs0342";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
