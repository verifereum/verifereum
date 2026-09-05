Theory vfmTest0233[no_sig_docs]
Ancestors vfmTestDefs0233
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0233_0.nsv", "result0233_1.nsv", "result0233_2.nsv", "result0233_3.nsv", "result0233_4.nsv", "result0233_5.nsv"];
val thyn = "vfmTestDefs0233";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
