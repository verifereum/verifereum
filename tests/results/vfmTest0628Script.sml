Theory vfmTest0628[no_sig_docs]
Ancestors vfmTestDefs0628
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0628_0.nsv"];
val thyn = "vfmTestDefs0628";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
