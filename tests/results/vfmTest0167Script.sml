Theory vfmTest0167[no_sig_docs]
Ancestors vfmTestDefs0167
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0167_0.nsv", "result0167_1.nsv", "result0167_2.nsv", "result0167_3.nsv", "result0167_4.nsv", "result0167_5.nsv"];
val thyn = "vfmTestDefs0167";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
