Theory vfmTest0109[no_sig_docs]
Ancestors vfmTestDefs0109
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0109_0.nsv", "result0109_1.nsv", "result0109_2.nsv"];
val thyn = "vfmTestDefs0109";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
