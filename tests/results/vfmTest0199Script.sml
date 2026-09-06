Theory vfmTest0199[no_sig_docs]
Ancestors vfmTestDefs0199
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0199_0.nsv", "result0199_1.nsv", "result0199_2.nsv", "result0199_3.nsv", "result0199_4.nsv", "result0199_5.nsv", "result0199_6.nsv", "result0199_7.nsv", "result0199_8.nsv", "result0199_9.nsv"];
val thyn = "vfmTestDefs0199";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
