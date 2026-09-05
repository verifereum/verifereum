Theory vfmTest0705[no_sig_docs]
Ancestors vfmTestDefs0705
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0705_0.nsv", "result0705_1.nsv"];
val thyn = "vfmTestDefs0705";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
