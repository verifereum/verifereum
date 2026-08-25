Theory vfmTest0099[no_sig_docs]
Ancestors vfmTestDefs0099
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0099_0.nsv", "result0099_1.nsv", "result0099_2.nsv", "result0099_3.nsv", "result0099_4.nsv", "result0099_5.nsv", "result0099_6.nsv", "result0099_7.nsv"];
val thyn = "vfmTestDefs0099";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
