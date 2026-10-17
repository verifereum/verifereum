Theory vfmTest0137[no_sig_docs]
Ancestors vfmTestDefs0137
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0137_0.nsv", "result0137_1.nsv", "result0137_2.nsv", "result0137_3.nsv", "result0137_4.nsv", "result0137_5.nsv", "result0137_6.nsv", "result0137_7.nsv", "result0137_8.nsv", "result0137_9.nsv", "result0137_10.nsv", "result0137_11.nsv"];
val thyn = "vfmTestDefs0137";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
